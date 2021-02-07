use std::borrow::Borrow;
use std::hash::Hash;
use std::collections::BTreeSet;

use rand::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use simple_bst::SimpleBSTSet;
// Looking to measure set implementation, not hasher performance so using a faster hasher
use fnv::FnvHashSet as HashSet;

use bst::BSTSet;

trait Set<T>: Default {
    fn len(&self) -> usize;

    fn contains<Q>(&self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn get<Q>(&self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn insert(&mut self, value: T) -> bool;

    fn remove<Q>(&mut self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;
}

macro_rules! impl_set {
    ($name:ident, $bound:ident $(+ $other_bound:ident)*) => {
        impl<T> Set<T> for $name<T>
            where T: $bound $(+ $other_bound)*,
        {
            fn len(&self) -> usize {
                $name::len(self)
            }

            fn contains<Q>(&self, value: &Q) -> bool
                where T: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::contains(self, value)
            }

            fn get<Q>(&self, value: &Q) -> Option<&T>
                where T: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get(self, value)
            }

            fn insert(&mut self, value: T) -> bool {
                $name::insert(self, value)
            }

            fn remove<Q>(&mut self, value: &Q) -> bool
                where T: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::remove(self, value)
            }
        }
    };
}

impl_set!(HashSet, Hash + Eq);
impl_set!(BTreeSet, Ord);
impl_set!(SimpleBSTSet, Ord);
impl_set!(BSTSet, Ord);

#[derive(Debug, Clone)]
struct Values {
    values: Vec<i64>,
}

impl Values {
    /// Deterministically generates a set of at least `nvalues` values
    ///
    /// All values are guaranteed to be unique and ordered randomly.
    pub fn generate(nvalues: u32) -> Self {
        // Want to spread values out so we generate interesting trees/tables.
        // Trying not to generate consecutive values or values that are strictly
        // increasing in magnitude.

        let mut values = Vec::new();

        let n = nvalues as i64;
        for i in 0..n {
            // [0..n] - n/2 = [-n/2..n/2]
            // [-n/2..n/2] * 4 = [-4n/2..4n/2]
            // Multiply by 4 so that numbers aren't consecutive
            let value = (i - n/2) * 10;
            values.push(value);
        }

        // Use seed to make this deterministic
        let mut rng = StdRng::seed_from_u64(45930923092);
        // Shuffle to ensure that values are in a uniformly random order
        values.shuffle(&mut rng);

        Self {values}
    }

    pub fn get(&self, value_i: i64) -> i64 {
        // Make sure index is >= 0
        let index = value_i.max(0);
        self.values[index as usize]
    }
}

fn slice_max<T: Copy + Ord>(data: &[T]) -> T {
    data.iter().max().copied().expect("bug: slice was empty")
}

/// Runs many consecutive inserts on a set
fn benchmark_inserts<M: Set<i64>>(values: &Values, inserts: usize) -> M {
    let mut set = M::default();

    for value_i in 0..inserts {
        black_box(set.insert(values.get(value_i as i64)));
    }

    set
}

/// Setup function for benchmark_gets
fn setup_benchmark_gets<M: Set<i64>>(values: &Values, gets: usize) -> M {
    let mut set = M::default();

    for value_i in 0..gets {
        black_box(set.insert(values.get(value_i as i64)));
    }

    set
}

/// Runs many consecutive get operations on a set
fn benchmark_gets<M: Set<i64>>(values: &Values, set: &mut M, gets: usize) {
    for i in 0..gets {
        // Get values in the opposite order to how they were inserted
        let value_i = gets - i - 1;
        let value = values.get(value_i as i64);
        black_box(set.get(&value));
        black_box(set.contains(&value));
    }
}

/// Setup function for benchmark_removes
fn setup_benchmark_removes<M: Set<i64>>(values: &Values, removes: usize) -> M {
    let mut set = M::default();

    for value_i in 0..removes {
        black_box(set.insert(values.get(value_i as i64)));
    }

    set
}

/// Runs many consecutive remove operations on a set
fn benchmark_removes<M: Set<i64>>(values: &Values, set: &mut M, removes: usize) {
    for i in 0..removes {
        // Remove values in the opposite order to how they were inserted
        let value_i = removes - i - 1;
        let value = values.get(value_i as i64);
        black_box(set.remove(&value));
        // Should always yield `false` since item has been removed
        black_box(set.remove(&value));
    }
}

/// Runs a bunch of operations on a set
fn benchmark_set_ops<M: Set<i64>>(values: &Values, steps: usize) -> M {
    const MAX_INSERTS: usize = 5;
    const MAX_GETS: usize = 3;
    const MAX_REMOVES: usize = 2;

    let mut set = M::default();

    let mut value_i = 0;
    for i in 0..steps {
        // Perform a few insertions
        let insertions = i % MAX_INSERTS;
        // Loop always runs at least once
        for _ in 0..=insertions {
            let value = values.get(value_i);
            value_i += 1;
            black_box(set.insert(value));
        }

        // Overwrite a previous insertion
        let value = values.get(value_i - 1);
        black_box(set.insert(value));

        // Try to get several values
        let gets = MAX_GETS - (i % MAX_GETS);
        for j in 0..gets {
            let value = values.get(value_i - j as i64);
            match set.get(&value) {
                Some(value) => black_box(value),
                None => continue, // ignore
            };
        }

        // Remove several values
        let removes = MAX_REMOVES - (i % MAX_REMOVES);
        for j in 0..removes {
            let value = values.get(value_i - j as i64);
            black_box(set.remove(&value));
        }
    }

    set
}

pub fn bench_set_insert(c: &mut Criterion) {
    const INSERTS: &[usize] = &[50, 100, 500, 1000, 2000];

    let values = Values::generate(slice_max(INSERTS) as u32);

    let mut group = c.benchmark_group("set insert");
    for inserts in INSERTS {
        group.bench_with_input(BenchmarkId::new("HashSet", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<HashSet<i64>>(&values, inserts))
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<BTreeSet<i64>>(&values, inserts))
        });
        group.bench_with_input(BenchmarkId::new("SimpleBSTSet", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<SimpleBSTSet<i64>>(&values, inserts))
        });
        group.bench_with_input(BenchmarkId::new("BSTSet", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<BSTSet<i64>>(&values, inserts))
        });
    }
    group.finish();
}

pub fn bench_set_get(c: &mut Criterion) {
    const GETS: &[usize] = &[50, 100, 500, 1000, 2000];

    let values = Values::generate(slice_max(GETS) as u32);

    let mut group = c.benchmark_group("set get");
    for gets in GETS {
        group.bench_with_input(BenchmarkId::new("HashSet", gets), gets, |b, &gets| {
            let mut set = setup_benchmark_gets(&values, gets);
            b.iter(|| benchmark_gets::<HashSet<i64>>(&values, &mut set, gets))
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", gets), gets, |b, &gets| {
            let mut set = setup_benchmark_gets(&values, gets);
            b.iter(|| benchmark_gets::<BTreeSet<i64>>(&values, &mut set, gets))
        });
        group.bench_with_input(BenchmarkId::new("SimpleBSTSet", gets), gets, |b, &gets| {
            let mut set = setup_benchmark_gets(&values, gets);
            b.iter(|| benchmark_gets::<SimpleBSTSet<i64>>(&values, &mut set, gets))
        });
        group.bench_with_input(BenchmarkId::new("BSTSet", gets), gets, |b, &gets| {
            let mut set = setup_benchmark_gets(&values, gets);
            b.iter(|| benchmark_gets::<BSTSet<i64>>(&values, &mut set, gets))
        });
    }
    group.finish();
}

pub fn bench_set_remove(c: &mut Criterion) {
    const REMOVES: &[usize] = &[50, 100, 500, 1000, 2000];

    let values = Values::generate(slice_max(REMOVES) as u32);

    let mut group = c.benchmark_group("set remove");
    for removes in REMOVES {
        group.bench_with_input(BenchmarkId::new("HashSet", removes), removes, |b, &removes| {
            let mut set = setup_benchmark_removes(&values, removes);
            b.iter(|| benchmark_removes::<HashSet<i64>>(&values, &mut set, removes))
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", removes), removes, |b, &removes| {
            let mut set = setup_benchmark_removes(&values, removes);
            b.iter(|| benchmark_removes::<BTreeSet<i64>>(&values, &mut set, removes))
        });
        group.bench_with_input(BenchmarkId::new("SimpleBSTSet", removes), removes, |b, &removes| {
            let mut set = setup_benchmark_removes(&values, removes);
            b.iter(|| benchmark_removes::<SimpleBSTSet<i64>>(&values, &mut set, removes))
        });
        group.bench_with_input(BenchmarkId::new("BSTSet", removes), removes, |b, &removes| {
            let mut set = setup_benchmark_removes(&values, removes);
            b.iter(|| benchmark_removes::<BSTSet<i64>>(&values, &mut set, removes))
        });
    }
    group.finish();
}

pub fn bench_set_ops(c: &mut Criterion) {
    const STEPS: &[usize] = &[50, 100, 1000, 2000, 4000];

    // Using (max * 5) because we do up to `MAX_INSERTS` inserts per step
    let values = Values::generate(slice_max(STEPS) as u32 * 5);

    let mut group = c.benchmark_group("set operations");
    for steps in STEPS {
        group.bench_with_input(BenchmarkId::new("HashSet", steps), steps, |b, &steps| {
            b.iter(|| benchmark_set_ops::<HashSet<i64>>(&values, steps))
        });
        group.bench_with_input(BenchmarkId::new("BTreeSet", steps), steps, |b, &steps| {
            b.iter(|| benchmark_set_ops::<BTreeSet<i64>>(&values, steps))
        });
        group.bench_with_input(BenchmarkId::new("SimpleBSTSet", steps), steps, |b, &steps| {
            b.iter(|| benchmark_set_ops::<SimpleBSTSet<i64>>(&values, steps))
        });
        group.bench_with_input(BenchmarkId::new("BSTSet", steps), steps, |b, &steps| {
            b.iter(|| benchmark_set_ops::<BSTSet<i64>>(&values, steps))
        });
    }
    group.finish();
}

criterion_group!(benches,
    bench_set_insert,
    bench_set_get,
    bench_set_remove,
    bench_set_ops,
);

criterion_main!(benches);
