//! Two sum - Given an array of integers and an integer target, return indices of the two numbers
//! that add up to the target. There is exactly one solution. Return the indices is any order.

use std::borrow::Borrow;
use std::hash::Hash;
use std::collections::BTreeMap;

use rand::prelude::*;
use rand::seq::SliceRandom;
use criterion::{
    BenchmarkGroup,
    BenchmarkId,
    Criterion,
    black_box,
    criterion_group,
    criterion_main,
    measurement::WallTime,
};
use simple_bst::SimpleBSTMap;
// Looking to measure map implementation, not hasher performance so using a faster hasher
use fnv::FnvHashMap as HashMap;

use bst::BSTMap;

trait Map<K, V>: Default {
    fn get<Q>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn contains_key<Q>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

macro_rules! impl_map {
    ($name:ident, $bound:ident $(+ $other_bound:ident)*) => {
        impl<K: Clone, V: Clone> Map<K, V> for $name<K, V>
            where K: $bound $(+ $other_bound)*,
        {
            fn get<Q>(&self, key: &Q) -> Option<&V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get(self, key)
            }

            fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get_mut(self, key)
            }

            fn contains_key<Q>(&self, key: &Q) -> bool
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::contains_key(self, key)
            }

            fn insert(&mut self, key: K, value: V) -> Option<V> {
                $name::insert(self, key, value)
            }
        }
    };
}

impl_map!(HashMap, Hash + Eq);
impl_map!(BTreeMap, Ord);
impl_map!(SimpleBSTMap, Ord);
impl_map!(BSTMap, Ord);

fn benchmark_two_sum<'a, M: Map<i64, usize>>(cases: &[(Vec<i64>, i64)]) {
    for &(ref numbers, target) in cases {
        black_box(two_sum::<M>(numbers, target));
    }
}

fn two_sum<M: Map<i64, usize>>(numbers: &[i64], target: i64) -> (usize, usize) {
    let mut seen = M::default();

    for (i, &num) in numbers.iter().enumerate() {
        let complement = target - num;
        if let Some(&j) = seen.get(&complement) {
            return (i, j);
        }
        seen.insert(num, i);
    }

    panic!("no solution")
}

/// Randomly generate multiple inputs for the two sum problem
fn generate_two_sum_inputs(nums_len: usize, cases_len: usize) -> Vec<(Vec<i64>, i64)> {
    // Use seed to make this deterministic
    let mut rng = StdRng::seed_from_u64(27645219);

    let mut cases = Vec::with_capacity(cases_len);

    for _ in 0..cases_len {
        cases.push(generate_two_sum_input(&mut rng, nums_len));
    }

    cases
}

/// Randomly generate the numbers array and target for the two sum problem
///
/// There will be exactly one solution
fn generate_two_sum_input(rng: &mut StdRng, len: usize) -> (Vec<i64>, i64) {
    assert!(len >= 2);

    let mut numbers = Vec::with_capacity(len);
    let target = rng.gen_range(32..=700);

    // Add in the solution
    let solution = rng.gen_range(1..=target/2);
    numbers.push(target - solution);
    numbers.push(solution);

    // Add in the remaining numbers
    for _ in 0..len-2 {
        // The remaining numbers are all greater than the target and thus cannot add up to the target
        numbers.push(rng.gen_range(target+1..=target+len as i64));
    }

    assert_eq!(numbers.len(), len);

    // Put the numbers in a random order
    for _ in 0..5 {
        numbers.shuffle(rng);
    }

    (numbers, target)
}

pub fn bench_two_sum(c: &mut Criterion) {
    const NUMS: &[usize] = &[500, 1000, 2000, 4000, 10000];
    const CASES: usize = 100;

    #[inline(always)]
    fn bench<M: Map<i64, usize>>(
        name: &'static str,
        group: &mut BenchmarkGroup<WallTime>,
        nums: &usize,
    ) {
        group.bench_with_input(BenchmarkId::new(name, nums), nums, |b, &nums| {
            let cases = generate_two_sum_inputs(nums, CASES);
            b.iter(|| benchmark_two_sum::<M>(&cases))
        });
    }

    let mut group = c.benchmark_group("map two sum");
    for nums in NUMS {
        bench::<HashMap<i64, usize>>("HashMap", &mut group, nums);
        bench::<BTreeMap<i64, usize>>("BTreeMap", &mut group, nums);
        bench::<SimpleBSTMap<i64, usize>>("SimpleBSTMap", &mut group, nums);
        bench::<BSTMap<i64, usize>>("BSTMap", &mut group, nums);
    }
    group.finish();
}

criterion_group!(benches,
    bench_two_sum,
);

criterion_main!(benches);
