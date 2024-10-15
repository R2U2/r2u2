use crate::internals::{bounds::*, types::{r2u2_infinity, r2u2_time, r2u2_verdict}};
use super::monitor::*;
use super::super::instructions::mltl::*;
use super::super::internals::debug::*;

#[cfg(embedded)]
use cortex_m_semihosting::hprintln;


pub struct SCQCtrlBlock{
    pub length: u32,
    pub write: usize,
    pub read1: usize,
    pub read2: usize,
    pub next_time: r2u2_time,
    pub temporal_block: SCQTemporalBlock,
    pub queue_ref: usize
}

impl Copy for SCQCtrlBlock{ }

impl Clone for SCQCtrlBlock{
    fn clone(&self) -> SCQCtrlBlock {
        return *self
    }
}

impl Default for SCQCtrlBlock{
    fn default() -> Self {
        return SCQCtrlBlock{
            length: 0,
            write: 0,
            read1: 0,
            read2: 0,
            next_time: 0,
            temporal_block: SCQTemporalBlock::default(),
            queue_ref: 0,
        }
    }
}

pub struct SCQTemporalBlock {
    pub lower_bound: r2u2_time,
    pub upper_bound: r2u2_time,
    pub edge: r2u2_time,
    pub previous: r2u2_verdict,
}

impl Copy for SCQTemporalBlock{ }

impl Clone for SCQTemporalBlock{
    fn clone(&self) -> SCQTemporalBlock {
        return *self
    }
}

impl Default for SCQTemporalBlock {
    fn default() -> Self {
        return SCQTemporalBlock {
            lower_bound: r2u2_infinity,
            upper_bound: r2u2_infinity,
            edge: 0,
            previous: r2u2_verdict{time: 0, truth: false}
        };
    }
}

pub struct SCQMemoryArena {
    pub control_blocks: [SCQCtrlBlock; R2U2_MAX_TL_INSTRUCTIONS],
    pub queue_mem: [r2u2_verdict; R2U2_TOTAL_QUEUE_MEM],
}

impl SCQMemoryArena{
    pub fn initialize() -> SCQMemoryArena{
        return SCQMemoryArena {
            control_blocks: [SCQCtrlBlock::default(); R2U2_MAX_TL_INSTRUCTIONS],
            queue_mem: [r2u2_verdict::default(); R2U2_TOTAL_QUEUE_MEM]
        }
    }
}

pub fn scq_write(monitor: &mut Monitor, queue_id: u32, verdict: r2u2_verdict){
    debug_print!("Before write:");
    print_scq(&monitor.queue_arena, queue_id);

    let queue_ctrl = &mut monitor.queue_arena.control_blocks[queue_id as usize];
    let prev: usize =  if queue_ctrl.write == 0 {queue_ctrl.length as usize - 1} else {queue_ctrl.write - 1};


    // Three checks:
    //    1: Is the new verdict the same as the previous? i.e. truth bit is clear
    //       in an xor and therefore the value is less than max time
    //    2: Coherence, if the previous timestamp matches the one under the write
    //       pointer, either this is the first write or we're in an incoherent
    //       state, write to the next cell instead.
    //    3: Queue is not empty, i.e., not `r2u2_infinity`
    if monitor.queue_arena.queue_mem[queue_ctrl.queue_ref+prev].truth == verdict.truth &&
            // queue_ctrl.write != prev as usize &&
            !(monitor.queue_arena.queue_mem[queue_ctrl.queue_ref+queue_ctrl.write].time == r2u2_infinity && queue_ctrl.write == 0){
        debug_print!("Compacting write");
        queue_ctrl.write = prev as usize;
    } 
  
    // Here the write offset is ready in all cases, write and advance
    monitor.queue_arena.queue_mem[queue_ctrl.queue_ref+queue_ctrl.write] = verdict;
    debug_print!("Write {} -> {} at write ptr {}", verdict.time, verdict.truth, queue_ctrl.write);
    // Yes, in the compacted case we're redoing what we undid, but ...
    queue_ctrl.write = (queue_ctrl.write + 1) % queue_ctrl.length as usize;

    debug_print!("After write:");
    print_scq(&monitor.queue_arena, queue_id);

}

// To-Do: Double check implementation... (Maybe should pass by reference for all...? So as to not create copies of values)
pub fn scq_read(monitor: &mut Monitor, parent_queue_id: u32, child_queue_id: u32, read_num: u8) -> (bool, r2u2_verdict){
    debug_print!("Reading:");
    print_scq(&monitor.queue_arena, child_queue_id);
    let child_queue_ctrl = monitor.queue_arena.control_blocks[child_queue_id as usize];
    let parent_queue_ctrl = &mut monitor.queue_arena.control_blocks[parent_queue_id as usize];
    let read = if read_num == 0 {&mut parent_queue_ctrl.read1} else {&mut parent_queue_ctrl.read2};

    if monitor.queue_arena.queue_mem[child_queue_ctrl.queue_ref + *read].time == r2u2_infinity && *read == 0 {
        // Empty Queue
        debug_print!("Empty queue");
        return (false, r2u2_verdict::default());
    }

    while {
        // Check if time pointed to is >= desired time
        if monitor.queue_arena.queue_mem[child_queue_ctrl.queue_ref + *read].time >= parent_queue_ctrl.next_time {
            debug_print!("New data found after scanning: ({}, {})", monitor.queue_arena.queue_mem[child_queue_ctrl.queue_ref + *read].truth, monitor.queue_arena.queue_mem[child_queue_ctrl.queue_ref + *read].time);
            return (true, monitor.queue_arena.queue_mem[child_queue_ctrl.queue_ref + *read]);
        }

        // Current slot is too old, step forward to check for new data
        *read = (*read + 1) % (child_queue_ctrl.length as usize);

        
        *read != child_queue_ctrl.write
    } {}

    // Here we hit the write pointer while scanning forwards, take a step back
    // in case the next value is compacted onto the slot we just checked.
    *read = if *read == 0 {child_queue_ctrl.length as usize - 1} else {*read - 1};

    // No new data in queue
    debug_print!("No new data!");
    return (false, r2u2_verdict::default());
}