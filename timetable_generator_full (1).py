#!/usr/bin/env python3
"""
Timetable Generator — Ultra-Robust Version for Handling Skewed Inputs

Features:
 - Extreme input validation with automatic correction
 - Handles impossible constraints through intelligent scaling
 - Graceful degradation when resources are insufficient
 - Comprehensive error recovery and suggestions
 - Works with any combination of inputs (even nonsensical ones)
"""

from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Set
from collections import defaultdict, deque
import math, json, csv, time, re

# ---------- constants ----------
WEEK_DAYS = ['Monday','Tuesday','Wednesday','Thursday','Friday']
MAX_PERIODS_PER_DAY = 12  # Reasonable upper limit
MIN_PERIODS_PER_DAY = 2   # Reasonable lower limit

# ---------- data classes ----------
@dataclass
class Subject:
    name: str
    hours_per_week: int
    is_lab: bool
    lab_name: Optional[str] = None
    fixed_slots: List[Tuple[str,int]] = field(default_factory=list)

    def __post_init__(self):
        if self.is_lab and not self.lab_name:
            self.lab_name = f"{self.name} Lab"

@dataclass
class Faculty:
    name: str
    subject_names: List[str]
    max_hours_per_day: int = 4
    max_hours_per_week: int = 20
    avg_leaves_per_month: float = 0.0
    expertise: Dict[str, float] = field(default_factory=dict)

@dataclass
class Room:
    name: str
    room_type: str
    capacity: int
    specialization: Optional[str] = None
    utilization_score: float = 0.0

# ---------- Ultra-Robust Input Handling ----------
def ultra_safe_int(value, name, default=1, min_val=0, max_val=1000):
    """Extremely safe integer conversion with bounds checking"""
    try:
        # Remove any non-numeric characters
        cleaned = re.sub(r'[^\d.-]', '', str(value))
        if not cleaned:
            print(f"Warning: Invalid {name}. Using default {default}.")
            return default
            
        val = int(float(cleaned))
        
        # Apply bounds
        if val < min_val:
            print(f"Warning: {name} too low ({val}). Setting to minimum {min_val}.")
            return min_val
        if val > max_val:
            print(f"Warning: {name} too high ({val}). Setting to maximum {max_val}.")
            return max_val
            
        return val
    except:
        print(f"Warning: Invalid {name}. Using default {default}.")
        return default

def ultra_safe_float(value, name, default=0.0, min_val=0.0, max_val=100.0):
    """Extremely safe float conversion with bounds checking"""
    try:
        cleaned = re.sub(r'[^\d.-]', '', str(value))
        if not cleaned:
            print(f"Warning: Invalid {name}. Using default {default}.")
            return default
            
        val = float(cleaned)
        
        if val < min_val:
            print(f"Warning: {name} too low ({val}). Setting to minimum {min_val}.")
            return min_val
        if val > max_val:
            print(f"Warning: {name} too high ({val}). Setting to maximum {max_val}.")
            return max_val
            
        return val
    except:
        print(f"Warning: Invalid {name}. Using default {default}.")
        return default

def normalize_string(s):
    """Normalize string for comparison"""
    return re.sub(r'[^\w]', '', str(s)).lower()

# ---------- scheduler ----------
class TimetableScheduler:
    def __init__(self, batches, faculties, rooms, periods_per_day, break_after, max_classes_per_day):
        self.batches = batches
        self.faculties = faculties
        self.rooms = rooms
        self.periods = periods_per_day
        self.break_after = break_after
        self.max_classes_per_day = max_classes_per_day

        # Initialize timetable
        self.timetable = {b: {d: {p: None for p in range(1, self.periods+1)} for d in WEEK_DAYS} for b in batches}

        # Initialize occupancy checks
        self.room_schedule = {r.name: {d: {p: False for p in range(1, self.periods+1)} for d in WEEK_DAYS} for r in rooms}
        self.faculty_schedule = {f.name: {d: {p: False for p in range(1, self.periods+1)} for d in WEEK_DAYS} for f in faculties}

        # Initialize loads
        self.faculty_load = {f.name: 0 for f in faculties}
        self.faculty_periods_assigned = {f.name: 0 for f in faculties}
        self.room_seat_usage = {r.name: 0 for r in rooms}

        # Tasks and scaling info
        self.tasks = {}
        self.scaling_info = {}
        
        # Decision log
        self.decision_log = []
        
        # Validation status
        self.validation_passed = False
        self.validation_warnings = []
        
        # Build indexes
        self.build_indexes()

    def build_indexes(self):
        """Build indexes for efficient lookups"""
        self.faculty_subject_index = defaultdict(list)
        for fac in self.faculties:
            for subj in fac.subject_names:
                self.faculty_subject_index[normalize_string(subj)].append(fac)
        
        self.room_capacity_index = defaultdict(list)
        for room in self.rooms:
            self.room_capacity_index[room.room_type].append(room)
        
        for room_type in self.room_capacity_index:
            self.room_capacity_index[room_type].sort(key=lambda r: r.capacity)

    def log_decision(self, batch, subject, faculty, room, day, period, reason):
        """Log scheduling decisions"""
        self.decision_log.append({
            'batch': batch,
            'subject': subject,
            'faculty': faculty,
            'room': room,
            'day': day,
            'period': period,
            'reason': reason
        })

    def effective_weekly_capacity(self, fac: Faculty) -> int:
        """Calculate effective weekly capacity"""
        reduction = min(0.5, fac.avg_leaves_per_month / (4.3 * 7))  # Cap at 50% reduction
        return max(1, int(fac.max_hours_per_week * (1 - reduction)))

    def ultra_validate_inputs(self) -> bool:
        """Ultra-robust input validation with automatic corrections"""
        errors = []
        warnings = []
        
        # Check for empty inputs
        if not self.batches:
            errors.append("No batches defined")
        if not self.faculties:
            errors.append("No faculties defined")
        if not self.rooms:
            errors.append("No rooms defined")
        
        # Check periods per day
        if self.periods < MIN_PERIODS_PER_DAY:
            warnings.append(f"Very few periods per day ({self.periods}). Consider increasing to at least {MIN_PERIODS_PER_DAY}.")
        elif self.periods > MAX_PERIODS_PER_DAY:
            warnings.append(f"Many periods per day ({self.periods}). Consider reducing to {MAX_PERIODS_PER_DAY} or less.")
        
        # Check batch strengths
        for bname, binfo in self.batches.items():
            if binfo['strength'] <= 0:
                errors.append(f"Batch {bname} has invalid strength: {binfo['strength']}")
            elif binfo['strength'] > 500:
                warnings.append(f"Batch {bname} has very large strength: {binfo['strength']}")
        
        # Check subject hours
        for bname, binfo in self.batches.items():
            for subj in binfo['subjects']:
                if subj.hours_per_week <= 0:
                    errors.append(f"Subject {subj.name} in batch {bname} has invalid hours: {subj.hours_per_week}")
                elif subj.hours_per_week > 50:
                    warnings.append(f"Subject {subj.name} in batch {bname} has very high hours: {subj.hours_per_week}")
        
        # Check faculty constraints
        for fac in self.faculties:
            if fac.max_hours_per_day <= 0:
                errors.append(f"Faculty {fac.name} has invalid max hours/day: {fac.max_hours_per_day}")
            if fac.max_hours_per_week <= 0:
                errors.append(f"Faculty {fac.name} has invalid max hours/week: {fac.max_hours_per_week}")
            if fac.max_hours_per_day > fac.max_hours_per_week:
                warnings.append(f"Faculty {fac.name} has daily max ({fac.max_hours_per_day}) > weekly max ({fac.max_hours_per_week})")
        
        # Check room capacities
        for room in self.rooms:
            if room.capacity <= 0:
                errors.append(f"Room {room.name} has invalid capacity: {room.capacity}")
            elif room.capacity > 1000:
                warnings.append(f"Room {room.name} has very large capacity: {room.capacity}")
        
        # Check faculty subject coverage
        all_subjects = set()
        for b in self.batches.values():
            all_subjects.update(s.name for s in b['subjects'])
        
        covered_subjects = set()
        for fac in self.faculties:
            covered_subjects.update(fac.subject_names)
        
        missing_subjects = all_subjects - covered_subjects
        if missing_subjects:
            errors.append(f"No faculty assigned for subjects: {', '.join(missing_subjects)}")
        
        # Check room capacity coverage
        for bname, binfo in self.batches.items():
            strength = binfo['strength']
            
            # Check classrooms
            classroom_capacity = max((r.capacity for r in self.rooms if r.room_type == 'classroom'), default=0)
            if classroom_capacity < strength:
                errors.append(f"Batch {bname} strength ({strength}) exceeds largest classroom capacity ({classroom_capacity})")
            
            # Check labs
            lab_needs = [(s.name, s.lab_name) for s in binfo['subjects'] if s.is_lab]
            for subj, lab_name in lab_needs:
                lab_capacity = max((r.capacity for r in self.rooms if r.room_type == 'lab' and r.specialization == lab_name), default=0)
                if lab_capacity < strength:
                    errors.append(f"Batch {bname} needs lab '{lab_name}' with capacity >= {strength} for subject {subj}")
        
        # Check total hours vs available slots
        total_hours_needed = sum(s.hours_per_week for b in self.batches.values() for s in b['subjects'])
        total_slots_available = len(self.batches) * self.periods * len(WEEK_DAYS)
        
        if total_hours_needed > total_slots_available * 3:  # More than 3x what's available
            warnings.append(f"Total hours needed ({total_hours_needed}) far exceeds available slots ({total_slots_available}). Heavy scaling required.")
        
        # Store warnings
        self.validation_warnings = warnings
        
        # Print validation results
        if errors:
            print("\n❌ Critical validation errors:")
            for error in errors:
                print(f" - {error}")
            self.validation_passed = False
            return False
        
        if warnings:
            print("\n⚠️ Validation warnings:")
            for warning in warnings:
                print(f" - {warning}")
        
        self.validation_passed = True
        return True

    def build_tasks(self):
        """Build tasks with aggressive scaling if needed"""
        tasks = {}
        scaling_info = {}
        
        for bname, binfo in self.batches.items():
            subjects = binfo['subjects']
            available_slots = self.periods * len(WEEK_DAYS)
            total_required = sum(s.hours_per_week for s in subjects)
            
            info = {
                'total_required': total_required,
                'available_slots': available_slots,
                'scaled': False,
                'original': {s.name: s.hours_per_week for s in subjects}
            }
            
            if total_required <= available_slots:
                for s in subjects:
                    fixed_count = sum(1 for (d,p) in s.fixed_slots if d in WEEK_DAYS and 1 <= p <= self.periods)
                    tasks[(bname, s.name)] = max(0, s.hours_per_week - fixed_count)
                scaling_info[bname] = info
                continue

            # Aggressive scaling needed
            info['scaled'] = True
            print(f"\n⚠️  Batch {bname}: Scaling required ({total_required} hours -> {available_slots} slots)")
            
            # Calculate proportional allocation
            alloc = {}
            remaining_slots = available_slots
            
            # First pass: assign minimum 1 slot to each subject
            for s in subjects:
                alloc[s.name] = 1
                remaining_slots -= 1
            
            # Second pass: distribute remaining slots proportionally
            if remaining_slots > 0:
                # Calculate remaining hours after minimum allocation
                remaining_hours = total_required - len(subjects)
                if remaining_hours > 0:
                    for s in subjects:
                        # Proportional allocation of remaining slots
                        proportion = s.hours_per_week / remaining_hours
                        additional = int(remaining_slots * proportion)
                        alloc[s.name] += additional
            
            # Ensure we don't exceed available slots
            total_allocated = sum(alloc.values())
            if total_allocated > available_slots:
                # Reduce proportionally
                reduction_factor = available_slots / total_allocated
                for s in subjects:
                    alloc[s.name] = max(1, int(alloc[s.name] * reduction_factor))
            
            # Final adjustment to match exactly available slots
            total_allocated = sum(alloc.values())
            if total_allocated < available_slots:
                # Add remaining slots to subjects with highest original hours
                sorted_subjects = sorted(subjects, key=lambda x: -x.hours_per_week)
                for i in range(available_slots - total_allocated):
                    alloc[sorted_subjects[i % len(sorted_subjects)].name] += 1
            
            # Subtract fixed slots
            for s in subjects:
                fixed_count = sum(1 for (d,p) in s.fixed_slots if d in WEEK_DAYS and 1 <= p <= self.periods)
                tasks[(bname, s.name)] = max(0, alloc[s.name] - fixed_count)
            
            info['scaled_allocation'] = alloc
            scaling_info[bname] = info
        
        self.tasks = tasks
        self.scaling_info = scaling_info
        return tasks

    def reserve_fixed_slots(self):
        """Reserve fixed slots with conflict resolution"""
        conflicts = []
        
        for bname, binfo in self.batches.items():
            strength = binfo['strength']
            for subj in binfo['subjects']:
                for (day, period) in subj.fixed_slots:
                    if day not in WEEK_DAYS or period < 1 or period > self.periods:
                        conflicts.append((bname, subj.name, day, period, "Invalid day/period"))
                        continue
                    
                    if self.timetable[bname][day][period] is not None:
                        conflicts.append((bname, subj.name, day, period, "Slot already occupied"))
                        continue
                    
                    # Find eligible faculty
                    eligible_fac = [f for f in self.faculties 
                                  if any(normalize_string(subj.name) == normalize_string(s) for s in f.subject_names)]
                    
                    chosen_fac = None
                    for f in sorted(eligible_fac, key=lambda x: self.faculty_load[x.name]):
                        if not self.faculty_schedule[f.name][day][period]:
                            chosen_fac = f
                            break
                    
                    if not chosen_fac:
                        conflicts.append((bname, subj.name, day, period, "No available faculty"))
                        continue
                    
                    # Find best-fit room
                    chosen_room = self.select_best_room(
                        'lab' if subj.is_lab else 'classroom', 
                        strength, 
                        day, 
                        period,
                        subj.lab_name if subj.is_lab else None
                    )
                    
                    if not chosen_room:
                        conflicts.append((bname, subj.name, day, period, "No suitable room"))
                        continue
                    
                    # Assign the slot
                    self.timetable[bname][day][period] = {
                        'subject': subj.lab_name if subj.is_lab else subj.name,
                        'faculty': chosen_fac.name,
                        'room': chosen_room.name,
                        'fixed': True
                    }
                    
                    # Update schedules
                    self.faculty_schedule[chosen_fac.name][day][period] = True
                    self.faculty_periods_assigned[chosen_fac.name] += 1
                    self.faculty_load[chosen_fac.name] += strength
                    self.room_schedule[chosen_room.name][day][period] = True
                    self.room_seat_usage[chosen_room.name] += min(strength, chosen_room.capacity)
                    
                    self.log_decision(bname, subj.name, chosen_fac.name, chosen_room.name, day, period, "Fixed slot")
        
        return conflicts

    def select_best_room(self, room_type, strength, day, period, specialization=None):
        """Select best room based on capacity and utilization"""
        eligible_rooms = []
        
        for room in self.room_capacity_index.get(room_type, []):
            if room.capacity < strength:
                continue
                
            if room_type == 'lab' and room.specialization != specialization:
                continue
                
            if self.room_schedule[room.name][day][period]:
                continue
                
            eligible_rooms.append(room)
        
        if not eligible_rooms:
            return None
        
        # Calculate utilization score
        for room in eligible_rooms:
            current_util = self.room_seat_usage[room.name] / max(1, room.capacity * self.periods * 5)
            room.utilization_score = current_util
        
        # Prefer rooms with lower utilization
        return min(eligible_rooms, key=lambda r: r.utilization_score)

    def rank_faculties(self, eligible_faculties, subject):
        """Rank faculties based on expertise and load"""
        ranked = []
        
        for fac in eligible_faculties:
            expertise = fac.expertise.get(subject, 1.0)
            load_factor = 1 / (1 + self.faculty_load[fac.name])
            score = expertise * load_factor
            ranked.append((fac, score))
        
        return [f for f, _ in sorted(ranked, key=lambda x: -x[1])]

    def schedule(self):
        """Main scheduling method with extreme robustness"""
        # Ultra-validate inputs
        if not self.ultra_validate_inputs():
            return [], {}, {}
        
        # Build tasks with aggressive scaling
        self.build_tasks()
        
        # Reserve fixed slots
        conflicts = self.reserve_fixed_slots()
        if conflicts:
            print(f"\n⚠️  Fixed slot conflicts found: {len(conflicts)}")
        
        # Map subjects to faculties
        subj_to_fac = {}
        for bname, binfo in self.batches.items():
            for subj in binfo['subjects']:
                key = (bname, subj.name)
                eligible = [f for f in self.faculties 
                          if any(normalize_string(subj.name) == normalize_string(s) for s in f.subject_names)]
                subj_to_fac[key] = eligible
        
        # Schedule
        batch_queue = deque(self.batches.keys())
        last_subject = {b: None for b in self.batches}
        
        for day in WEEK_DAYS:
            per_batch_day_count = {b: 0 for b in self.batches}
            batch_queue.rotate(-1)
            
            for period in range(1, self.periods+1):
                batch_queue.rotate(-1)
                
                for bname in list(batch_queue):
                    if self.timetable[bname][day][period] is not None:
                        continue
                    
                    if per_batch_day_count[bname] >= self.max_classes_per_day:
                        continue
                    
                    # Get candidate subjects
                    candidates = []
                    for subj in self.batches[bname]['subjects']:
                        rem = self.tasks.get((bname, subj.name), 0)
                        if rem > 0:
                            candidates.append((rem, subj))
                    
                    if not candidates:
                        continue
                    
                    # Sort by remaining hours
                    candidates.sort(key=lambda x: -x[0])
                    assigned = False
                    
                    for _, subj in candidates:
                        # Avoid same subject consecutively if possible
                        if last_subject[bname] == subj.name and len(candidates) > 1:
                            continue
                        
                        key = (bname, subj.name)
                        eligible = subj_to_fac.get(key, [])
                        
                        # Filter available faculty
                        elig2 = []
                        for f in eligible:
                            if self.faculty_schedule[f.name][day][period]:
                                continue
                                
                            daily_assigned = sum(1 for p in range(1, self.periods+1) 
                                               if self.faculty_schedule[f.name][day][p])
                            if daily_assigned >= f.max_hours_per_day:
                                continue
                                
                            if self.faculty_periods_assigned[f.name] >= self.effective_weekly_capacity(f):
                                continue
                                
                            elig2.append(f)
                        
                        if not elig2:
                            continue
                        
                        # Select best faculty
                        ranked_fac = self.rank_faculties(elig2, subj.name)
                        chosen_fac = ranked_fac[0]
                        
                        # Select best room
                        chosen_room = self.select_best_room(
                            'lab' if subj.is_lab else 'classroom', 
                            self.batches[bname]['strength'], 
                            day, 
                            period,
                            subj.lab_name if subj.is_lab else None
                        )
                        
                        if not chosen_room:
                            continue
                        
                        # Assign
                        self.timetable[bname][day][period] = {
                            'subject': subj.lab_name if subj.is_lab else subj.name,
                            'faculty': chosen_fac.name,
                            'room': chosen_room.name,
                            'fixed': False
                        }
                        
                        # Update schedules
                        self.faculty_schedule[chosen_fac.name][day][period] = True
                        self.faculty_periods_assigned[chosen_fac.name] += 1
                        self.faculty_load[chosen_fac.name] += self.batches[bname]['strength']
                        self.room_schedule[chosen_room.name][day][period] = True
                        self.room_seat_usage[chosen_room.name] += min(
                            self.batches[bname]['strength'], 
                            chosen_room.capacity
                        )
                        
                        # Update tasks
                        self.tasks[key] -= 1
                        last_subject[bname] = subj.name
                        per_batch_day_count[bname] += 1
                        assigned = True
                        
                        self.log_decision(bname, subj.name, chosen_fac.name, chosen_room.name, day, period, "Regular")
                        
                        break
        
        # Handle remaining unassigned
        unassigned = {k:v for k,v in self.tasks.items() if v>0}
        relaxed = self.relax_constraints(unassigned)
        
        # Analyze results
        reasons = defaultdict(list)
        for (bname,sname),cnt in unassigned.items():
            # Check for faculty issues
            any_fac = any(normalize_string(sname) in [normalize_string(sn) for sn in f.subject_names] 
                         for f in self.faculties)
            if not any_fac:
                reasons['no_faculty'].append((bname,sname,cnt))
                continue
            
            # Check for room issues
            subj = next((x for x in self.batches[bname]['subjects'] if x.name==sname), None)
            if subj:
                if subj.is_lab:
                    ok = any(r for r in self.rooms 
                           if r.room_type=='lab' and 
                           r.specialization == subj.lab_name and 
                           r.capacity >= self.batches[bname]['strength'])
                    if not ok:
                        reasons['no_lab_room'].append((bname,sname,cnt))
                        continue
                else:
                    ok = any(r for r in self.rooms 
                           if r.room_type=='classroom' and 
                           r.capacity >= self.batches[bname]['strength'])
                    if not ok:
                        reasons['no_classroom_capacity'].append((bname,sname,cnt))
                        continue
            
            reasons['insufficient_slots'].append((bname,sname,cnt))
        
        diagnostics = {
            'scaling_info': self.scaling_info,
            'total_tasks': sum(v for v in self.tasks.values()),
            'available_slots': len(self.batches)*self.periods*len(WEEK_DAYS),
            'conflicts': conflicts,
            'relaxed': relaxed,
            'warnings': self.validation_warnings
        }
        
        return unassigned, reasons, diagnostics

    def relax_constraints(self, unassigned):
        """Try to relax constraints for unassigned periods"""
        relaxed = []
        
        for (batch, subject), count in list(unassigned.items()):
            if count <= 0:
                continue
                
            # Try to find any available slot
            for day in WEEK_DAYS:
                for period in range(1, self.periods+1):
                    if self.timetable[batch][day][period] is None:
                        subj = next((s for s in self.batches[batch]['subjects'] if s.name == subject), None)
                        if not subj:
                            continue
                            
                        # Find any available faculty
                        eligible = [f for f in self.faculties 
                                  if any(normalize_string(subj.name) == normalize_string(s) for s in f.subject_names)]
                        
                        elig2 = [f for f in eligible 
                               if not self.faculty_schedule[f.name][day][period]]
                        
                        if not elig2:
                            continue
                            
                        # Select least loaded faculty
                        chosen_fac = min(elig2, key=lambda f: self.faculty_load[f.name])
                        
                        # Select any available room
                        chosen_room = self.select_best_room(
                            'lab' if subj.is_lab else 'classroom', 
                            self.batches[batch]['strength'], 
                            day, 
                            period,
                            subj.lab_name if subj.is_lab else None
                        )
                        
                        if not chosen_room:
                            continue
                            
                        # Assign
                        self.timetable[batch][day][period] = {
                            'subject': subj.lab_name if subj.is_lab else subj.name,
                            'faculty': chosen_fac.name,
                            'room': chosen_room.name,
                            'fixed': False
                        }
                        
                        # Update schedules
                        self.faculty_schedule[chosen_fac.name][day][period] = True
                        self.faculty_periods_assigned[chosen_fac.name] += 1
                        self.faculty_load[chosen_fac.name] += self.batches[batch]['strength']
                        self.room_schedule[chosen_room.name][day][period] = True
                        self.room_seat_usage[chosen_room.name] += min(
                            self.batches[batch]['strength'], 
                            chosen_room.capacity
                        )
                        
                        # Update tasks
                        self.tasks[(batch, subject)] -= 1
                        relaxed.append((batch, subject, day, period, "Relaxed constraint"))
                        break
                
                if self.tasks[(batch, subject)] < count:
                    break
        
        return relaxed

    # ---------- Output methods ----------
    def print_timetable(self):
        if not self.validation_passed:
            print("\nCannot print timetable - validation failed.")
            return
            
        for bname in self.batches:
            strength = self.batches[bname]['strength']
            print("\n" + "="*90)
            print(f"Timetable for {bname} (Strength: {strength})")
            print("="*90)
            header = "Day".ljust(12) + " | " + " | ".join(f"P{p}".center(18) for p in range(1,self.periods+1))
            print(header)
            print("-"*len(header))
            
            for d in WEEK_DAYS:
                row = d.ljust(12) + " | "
                cells = []
                for p in range(1, self.periods+1):
                    ent = self.timetable[bname][d][p]
                    if ent is None:
                        cells.append("Free".center(18))
                    else:
                        subj = ent.get('subject','')
                        fac = ent.get('faculty') or "TBD"
                        room = ent.get('room') or "TBD"
                        fixed = " (F)" if ent.get('fixed') else ""
                        cells.append(f"{subj[:12]} / {fac[:8]} / {room}{fixed}".center(18))
                row += " | ".join(cells)
                print(row)

    def print_summary(self):
        if not self.validation_passed:
            print("\nCannot print summary - validation failed.")
            return
            
        print("\n=== Faculty Load Summary ===")
        total_load = sum(self.faculty_load.values()) or 1
        avg = total_load / max(1, len(self.faculty_load))
        
        for f in self.faculties:
            load = self.faculty_load[f.name]
            periods = self.faculty_periods_assigned[f.name]
            capacity = self.effective_weekly_capacity(f)
            pct = periods/capacity*100 if capacity else 0
            flag = " ⚠️" if pct > 90 else ""
            print(f" - {f.name}: {periods}/{capacity} periods ({pct:.1f}%) load={load} students{flag}")

        print("\n=== Room Utilization ===")
        total_slots = len(WEEK_DAYS) * self.periods
        
        for r in self.rooms:
            used = sum(1 for d in WEEK_DAYS for p in range(1, self.periods+1) 
                      if self.room_schedule[r.name][d][p])
            seat_used = self.room_seat_usage[r.name]
            possible = r.capacity * total_slots
            pct = seat_used/possible*100 if possible else 0
            print(f" - {r.name} ({r.room_type}, cap {r.capacity}): {used}/{total_slots} slots, {seat_used}/{possible} seats ({pct:.1f}%)")

    def export_json(self, path="timetable_export.json"):
        out = {
            'periods_per_day': self.periods,
            'days': WEEK_DAYS,
            'batches': {},
            'scaling_info': self.scaling_info,
            'faculty_load': self.faculty_load,
            'room_seat_usage': self.room_seat_usage,
            'decision_log': self.decision_log,
            'validation_passed': self.validation_passed,
            'warnings': self.validation_warnings
        }
        
        for b in self.batches:
            out['batches'][b] = {
                'strength': self.batches[b]['strength'],
                'timetable': {}
            }
            for d in WEEK_DAYS:
                out['batches'][b]['timetable'][d] = {}
                for p in range(1, self.periods+1):
                    out['batches'][b]['timetable'][d][f"P{p}"] = self.timetable[b][d][p]
        
        with open(path,'w',encoding='utf-8') as fh:
            json.dump(out, fh, indent=2)
        print(f"Exported JSON -> {path}")

    def export_csv(self, path="timetable_export.csv"):
        rows = []
        for b in self.batches:
            for d in WEEK_DAYS:
                for p in range(1, self.periods+1):
                    ent = self.timetable[b][d][p]
                    rows.append({
                        'batch': b,
                        'day': d,
                        'period': p,
                        'subject': ent.get('subject') if ent else '',
                        'faculty': ent.get('faculty') if ent else '',
                        'room': ent.get('room') if ent else '',
                        'fixed': ent.get('fixed') if ent else False
                    })
        
        with open(path,'w',newline='',encoding='utf-8') as fh:
            writer = csv.DictWriter(fh, fieldnames=['batch','day','period','subject','faculty','room','fixed'])
            writer.writeheader()
            writer.writerows(rows)
        print(f"Exported CSV -> {path}")

# ---------- Ultra-Robust Input Prompts ----------
def prompt_batches():
    batches = {}
    nb = ultra_safe_int(input("Number of batches (e.g. 2): "), "Number of batches", 1, 1, 20)
    
    for i in range(1, nb+1):
        print(f"\n--- Batch {i} ---")
        bname = input(f"Batch name [B{i}]: ").strip() or f"B{i}"
        strength = ultra_safe_int(
            input(f"Batch strength (students) for {bname} [30]: "),
            "Batch strength", 30, 1, 1000
        )
        
        nsub = ultra_safe_int(
            input(f"Number of subjects for {bname} [3]: "),
            "Number of subjects", 3, 1, 20
        )
        
        subjects = []
        for j in range(1, nsub+1):
            print(f"\n  Subject {j}:")
            sname = input(f"   Name [Sub{j}]: ").strip() or f"Sub{j}"
            hours = ultra_safe_int(
                input(f"   Hours/week for {sname} [3]: "),
                "Hours per week", 3, 1, 50
            )
            
            is_lab = input(f"   Is {sname} a lab? (y/N): ").strip().lower() == 'y'
            lab_name = None
            
            if is_lab:
                lab_name = input(f"   Lab name for {sname} [{sname} Lab]: ").strip() or f"{sname} Lab"
            
            fixed_raw = input(f"   Any fixed slots for {sname}? (e.g. Mon:1,Tue:3 or Enter to skip): ").strip()
            fixed_slots = []
            
            if fixed_raw:
                for part in fixed_raw.split(','):
                    part = part.strip()
                    if ':' in part:
                        d, p = part.split(':', 1)
                        d = d.strip().title()
                        pnum = ultra_safe_int(p.strip(), "Period number", 1, 1, 50)
                        if d in WEEK_DAYS:
                            fixed_slots.append((d, pnum))
                        else:
                            print(f"   Warning: Invalid day '{d}' - skipping")
            
            subjects.append(Subject(sname, hours, is_lab, lab_name, fixed_slots))
        
        batches[bname] = {'strength': strength, 'subjects': subjects}
    
    return batches

def prompt_rooms():
    rooms = []
    n = ultra_safe_int(
        input("Total number of rooms (classrooms + labs) [3]: "),
        "Number of rooms", 3, 1, 50
    )
    
    room_names = set()
    
    for i in range(1, n+1):
        print(f"\n--- Room {i} ---")
        while True:
            name = input(f"Room name [Room-{i}]: ").strip() or f"Room-{i}"
            if name in room_names:
                print(f"Error: Room name '{name}' already exists.")
            else:
                room_names.add(name)
                break
        
        while True:
            rtype = input(f"Room type (classroom/lab) [classroom]: ").strip().lower()
            if rtype in ('classroom', 'lab'):
                rtype = 'lab' if rtype == 'lab' else 'classroom'
                break
            print("Please enter either 'classroom' or 'lab'")
        
        cap = ultra_safe_int(
            input(f"Capacity for {name} [30]: "),
            "Room capacity", 30, 1, 1000
        )
        
        spec = None
        if rtype == 'lab':
            spec = input(f"Specialization for {name} (press Enter to use room name): ").strip() or name
        
        rooms.append(Room(name, rtype, cap, spec))
    
    return rooms

def prompt_faculties(all_subjects):
    faculties = []
    n = ultra_safe_int(
        input("Number of faculties [3]: "),
        "Number of faculties", 3, 1, 50
    )
    
    faculty_names = set()
    
    print("\nAvailable subjects:")
    for idx, s in enumerate(all_subjects):
        print(f" [{idx}] {s}")
    
    for i in range(1, n+1):
        print(f"\n--- Faculty {i} ---")
        while True:
            fname = input(f"Faculty name [F{i}]: ").strip() or f"F{i}"
            if fname in faculty_names:
                print(f"Error: Faculty name '{fname}' already exists.")
            else:
                faculty_names.add(fname)
                break
        
        while True:
            raw = input(f"Enter subject indices/names {fname} can teach (comma-separated): ").strip()
            if not raw:
                print("Error: At least one subject must be selected")
                continue
                
            chosen = []
            errors = []
            
            for tok in raw.split(','):
                tok = tok.strip()
                if not tok:
                    continue
                    
                if tok.isdigit():
                    k = int(tok)
                    if 0 <= k < len(all_subjects):
                        chosen.append(all_subjects[k])
                    else:
                        errors.append(f"Invalid subject index: {tok}")
                else:
                    token_l = normalize_string(tok)
                    matches = [s for s in all_subjects if normalize_string(s) == token_l]
                    if matches:
                        chosen.extend(matches)
                    else:
                        partial_matches = [s for s in all_subjects if normalize_string(s).startswith(token_l)]
                        if len(partial_matches) == 1:
                            chosen.append(partial_matches[0])
                        elif len(partial_matches) > 1:
                            errors.append(f"Ambiguous subject '{tok}' (matches: {', '.join(partial_matches)})")
                        else:
                            errors.append(f"Unknown subject '{tok}'")
            
            if errors:
                print("Errors in subject selection:")
                for err in errors:
                    print(f" - {err}")
                continue
                
            if not chosen:
                print("Error: No valid subjects selected")
                continue
                
            break
        
        max_d = ultra_safe_int(
            input(f"Max hours/day for {fname} [4]: "),
            "Max hours per day", 4, 1, 12
        )
        
        max_w = ultra_safe_int(
            input(f"Max hours/week for {fname} [20]: "),
            "Max hours per week", 20, 1, 60
        )
        
        leaves = ultra_safe_float(
            input(f"Average leaves/month for {fname} [0]: "),
            "Leaves per month", 0.0, 0.0, 20.0
        )
        
        # Collect expertise scores
        expertise = {}
        print("\nExpertise scores (1.0 = expert, 0.5 = moderate, 0.1 = beginner)")
        for subj in chosen:
            score = ultra_safe_float(
                input(f"   Expertise for {subj} [1.0]: "),
                "Expertise score", 1.0, 0.0, 1.0
            )
            expertise[subj] = score
        
        faculties.append(Faculty(fname, chosen, max_d, max_w, leaves, expertise))
    
    return faculties

# ---------- main ----------
def main():
    print("=== Ultra-Robust Timetable Generator ===")
    print("Handles any input, even nonsensical ones!\n")
    
    # Simple login
    user = input("Username: ").strip()
    pwd = input("Password: ").strip()
    if user != 'admin' or pwd != 'admin123':
        print("Invalid credentials (use admin/admin123). Exiting.")
        return

    periods = ultra_safe_int(
        input("Number of periods per day [8]: "),
        "Periods per day", 8, MIN_PERIODS_PER_DAY, MAX_PERIODS_PER_DAY
    )
    
    break_after = ultra_safe_int(
        input("Break after which period? (0 = no break) [4]: "),
        "Break period", 0, 0, periods-1
    )
    
    max_classes = ultra_safe_int(
        input("Max classes per day per batch [6]: "),
        "Max classes per day", 6, 1, periods
    )

    print("\n--- Batch Configuration ---")
    batches = prompt_batches()
    
    # Build subject list
    all_subjects = []
    seen = set()
    for b in batches:
        for s in batches[b]['subjects']:
            if s.name not in seen:
                all_subjects.append(s.name)
                seen.add(s.name)
    
    print("\n--- Room Configuration ---")
    rooms = prompt_rooms()
    
    print("\n--- Faculty Configuration ---")
    faculties = prompt_faculties(all_subjects)

    print("\nInitializing scheduler...")
    sched = TimetableScheduler(batches, faculties, rooms, periods, break_after, max_classes)
    
    print("\nGenerating timetable...")
    start_time = time.time()
    unassigned, reasons, diagnostics = sched.schedule()
    elapsed = time.time() - start_time
    
    print(f"\nTimetable generated in {elapsed:.2f} seconds")
    
    if sched.validation_passed:
        sched.print_timetable()
        
        print("\n=== Diagnostics ===")
        if diagnostics.get('scaling_info'):
            for b, info in diagnostics['scaling_info'].items():
                if info.get('scaled'):
                    print(f" - Batch {b} scaled: {info['original']} -> {info['scaled_allocation']}")
        
        if unassigned:
            print(f"\n⚠️  Unassigned periods: {sum(unassigned.values())}")
            print("\nSuggestions:")
            if reasons.get('no_faculty'):
                print(" - Add faculty for missing subjects")
            if reasons.get('no_lab_room'):
                print(" - Add labs with required specializations")
            if reasons.get('no_classroom_capacity'):
                print(" - Add larger classrooms")
            if reasons.get('insufficient_slots'):
                print(" - Increase periods per day or reduce subject hours")
        else:
            print("\n✅ All periods scheduled successfully!")

        sched.print_summary()
    else:
        print("\n❌ Timetable generation failed due to critical errors.")
    
    if input("\nExport JSON? (y/N): ").strip().lower() == 'y':
        fname = input("Filename [timetable_export.json]: ").strip() or "timetable_export.json"
        sched.export_json(fname)
    
    if input("Export CSV? (y/N): ").strip().lower() == 'y':
        fname = input("Filename [timetable_export.csv]: ").strip() or "timetable_export.csv"
        sched.export_csv(fname)
    
    print("\nDone.")

if __name__ == "__main__":
    main()
