use std::alloc::{alloc_zeroed, handle_alloc_error, Layout};
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

const LAP: usize = 64;
const BLOCK_CAP: usize = LAP - 1;
const SHIFT: usize = 1;
const WRITE: usize = 1;

#[repr(align(128))]
struct CachePadded<T>(T);

impl<T> CachePadded<T> {
    fn new(value: T) -> Self {
        Self(value)
    }
}

impl<T> std::ops::Deref for CachePadded<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

struct Slot<T> {
    task: UnsafeCell<MaybeUninit<T>>,
    state: AtomicUsize,
}

struct Block<T> {
    next: AtomicPtr<Block<T>>,
    slots: [Slot<T>; BLOCK_CAP],
}

impl<T> Block<T> {
    const LAYOUT: Layout = Layout::new::<Self>();

    fn new() -> Box<Self> {
        let ptr = unsafe { alloc_zeroed(Self::LAYOUT) };
        if ptr.is_null() {
            handle_alloc_error(Self::LAYOUT);
        }
        unsafe { Box::from_raw(ptr.cast()) }
    }
}

struct Position<T> {
    index: AtomicUsize,
    block: AtomicPtr<Block<T>>,
}

struct Injector<T> {
    tail: CachePadded<Position<T>>,
    _marker: PhantomData<T>,
}

impl<T> Injector<T> {
    fn new() -> Self {
        let block = Box::into_raw(Block::<T>::new());
        Self {
            tail: CachePadded::new(Position {
                block: AtomicPtr::new(block),
                index: AtomicUsize::new(0),
            }),
            _marker: PhantomData,
        }
    }

    fn push(&self) {
        let mut tail = self.tail.index.load(Ordering::Acquire);
        let mut block = self.tail.block.load(Ordering::Acquire);
        let mut next_block = None;
        loop {
            let offset = (tail >> SHIFT) % LAP;
            if offset + 1 == BLOCK_CAP && next_block.is_none() {
                next_block = Some(Block::<T>::new());
            }
            let new_tail = tail + (1 << SHIFT);
            match self.tail.index.compare_exchange_weak(
                tail,
                new_tail,
                Ordering::SeqCst,
                Ordering::Acquire,
            ) {
                Ok(_) => unsafe {
                    if offset + 1 == BLOCK_CAP {
                        let next_block = Box::into_raw(next_block.unwrap());
                        let next_index = new_tail.wrapping_add(1 << SHIFT);
                        self.tail.block.store(next_block, Ordering::Release);
                        self.tail.index.store(next_index, Ordering::Release);
                        (*block).next.store(next_block, Ordering::Release);
                    }
                    let slot = (*block).slots.get_unchecked(offset);
                    slot.state.fetch_or(WRITE, Ordering::Release);
                    return;
                },
                Err(t) => {
                    tail = t;
                    block = self.tail.block.load(Ordering::Acquire);
                }
            }
        }
    }
}

fn main() {
    let q = Injector::<i32>::new();
    q.push();
    mem::forget(q);
    println!("ok");
}
