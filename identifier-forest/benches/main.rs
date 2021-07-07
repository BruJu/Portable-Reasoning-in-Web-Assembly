use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use identifier_forest::compile_time_forest::profile4::*;
use identifier_forest::order::{ Position, Subject, Predicate, Object, Graph };

use identifier_forest::compile_time_forest::CTForest;
use identifier_forest::tree::Forest4;
use identifier_forest::tree::MaybeTree4;
use identifier_forest::run_time_forest::IndexingForest4;


extern crate if_pac;
use if_pac::quad::{
    GSPOGreedy, GSPOLazy, Order, QuadForest, QuadForestProfile, RuntimeFat, RuntimeSlim,
};

type RTForest = IndexingForest4<usize>;

type CTForestLazy = CTForest<usize,
    GPSOAlways, SPOG, PGSO, OPSG, SOGP, GOPS
>;

type CTForestGreedy = CTForest<usize,
    GPSOAlways, SPOGAlways, PGSOAlways, OPSGAlways, SOGPAlways, GOPSAlways
>;

type CTForestLazyGoodOrder = CTForest<usize,
    SPOGAlways, GPSO, PGSO, OPSG, SOGP, GOPS
>;

const S: usize = Subject::VALUE;
const P: usize = Predicate::VALUE;
const O: usize = Object::VALUE;
const G: usize = Graph::VALUE;

fn load_lazy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Load lazy");
    
    group.bench_function("JB Runtime Enum", |b| {
        b.iter(|| {
            load_into(&mut RTForest::new_with_indexes(
                &[[G,S,P,O]],
                &[[S,P,O,G], [P,G,S,O], [O,P,S,G], [S,O,G,P], [G,O,P,S]],
            ))
        })
    });
    group.bench_function("JB Compile time", |b| {
        b.iter(|| load_into(&mut CTForestLazy::new()))
    });
    group.bench_function("JB CTForestLazyGoodOrder", |b| {
        b.iter(|| load_into(&mut CTForestLazyGoodOrder::new()))
    });

    group.bench_function("PAC Runtime fat", |b| {
        b.iter(|| {
            load_into_pac(&mut QuadForest::<RuntimeFat>::new_rt(
                &[Order::GSPO],
                &[Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS],
            ))
        })
    });
    group.bench_function("PAC Runtime slim", |b| {
        b.iter(|| {
            load_into_pac(&mut QuadForest::<RuntimeSlim>::new_rt(
                &[Order::GSPO],
                &[Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS],
            ))
        })
    });
    group.bench_function("PAC Compile time", |b| {
        b.iter(|| load_into_pac(&mut QuadForest::<GSPOLazy>::new()))
    });
    
    group.finish();
}

fn load_greedy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Load greedy");
    
    group.bench_function("JB Runtime Enum", |b| {
        b.iter(|| {
            load_into(&mut RTForest::new_with_indexes(
                &[[G,S,P,O], [S,P,O,G], [P,G,S,O], [O,P,S,G], [S,O,G,P], [G,O,P,S]], &[]
            ))
        })
    });
    group.bench_function("JB Compile time", |b| {
        b.iter(|| load_into(&mut CTForestGreedy::new()))
    });

    group.bench_function("PAC Runtime fat", |b| {
        b.iter(|| {
            load_into_pac(&mut QuadForest::<RuntimeFat>::new_rt(
                &[Order::GSPO, Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS],
                &[],
            ))
        })
    });
    group.bench_function("PAC Runtime slim", |b| {
        b.iter(|| {
            load_into_pac(&mut QuadForest::<RuntimeSlim>::new_rt(
                &[Order::GSPO, Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS],
                &[],
            ))
        })
    });
    group.bench_function("PAC Compile time", |b| {
        b.iter(|| load_into_pac(&mut QuadForest::<GSPOGreedy>::new()))
    });

    group.finish();
}

fn search_lazy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Search lazy");
    
    group.bench_function("JB Runtime Enum", |b| {
        b.iter_batched(
            || {
                let mut forest =
                RTForest::new_with_indexes(
                    &[[G,S,P,O]],
                    &[[S,P,O,G], [P,G,S,O], [O,P,S,G], [S,O,G,P], [G,O,P,S]],
                );
                load_into(&mut forest);
                forest
            },
            |forest| {
                forest
                    .get_quads([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("JB Compile time", |b| {
        b.iter_batched(
            || {
                let mut forest = CTForestLazy::new();
                load_into(&mut forest);
                forest
            },
            |forest| {
                forest
                    .get_quads([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("JB CTForestLazyGoodOrder", |b| {
        b.iter_batched(
            || {
                let mut forest = CTForestLazyGoodOrder::new();
                load_into(&mut forest);
                forest
            },
            |forest| {
                forest
                    .get_quads([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });

    
    group.bench_function("PAC Runtime fat", |b| {
        b.iter_batched(
            || {
                let mut forest =
                QuadForest::<RuntimeFat>::new_rt(
                    &[Order::GSPO],
                    &[Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS],        
                );
                load_into_pac(&mut forest);
                forest
            },
            |forest| {
                forest
                    .iter_matching([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("PAC Runtime slim", |b| {
        b.iter_batched(
            || {
                let mut forest =
                QuadForest::<RuntimeSlim>::new_rt(
                    &[Order::GSPO],
                    &[Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS],        
                );
                load_into_pac(&mut forest);
                forest
            },
            |forest| {
                forest
                    .iter_matching([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("PAC Compile time", |b| {
        b.iter_batched(
            || {
                let mut forest = QuadForest::<GSPOLazy>::new();
                load_into_pac(&mut forest);
                forest
            },
            |forest| {
                forest
                    .iter_matching([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn search_prebuilt(c: &mut Criterion) {
    let mut group = c.benchmark_group("Search prebuilt");

    let mut forest = RTForest::new_with_indexes(
        &[[G,S,P,O], [S,P,O,G], [P,G,S,O], [O,P,S,G], [S,O,G,P], [G,O,P,S]], &[]
    );
    load_into(&mut forest);
    group.bench_with_input("JB Runtime Enum", &forest, |b, forest| {
        b.iter(|| {
            forest
                .get_quads([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    let mut forest = CTForestGreedy::new();
    load_into(&mut forest);
    group.bench_with_input("JB Compile time", &forest, |b, forest| {
        b.iter(|| {
            forest
                .get_quads([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    let mut forest = QuadForest::<RuntimeFat>::new_rt(&[Order::GSPO, Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS], &[]);
    load_into_pac(&mut forest);
    group.bench_with_input("PAC Runtime fat", &forest, |b, forest| {
        b.iter(|| {
            forest
                .iter_matching([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    let mut forest = QuadForest::<RuntimeSlim>::new_rt(&[Order::GSPO, Order::SPOG, Order::PGSO, Order::OPSG, Order::SOGP, Order::GOPS], &[]);
    load_into_pac(&mut forest);
    group.bench_with_input("PAC Runtime slim", &forest, |b, forest| {
        b.iter(|| {
            forest
                .iter_matching([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    let mut forest = QuadForest::<GSPOGreedy>::new();
    load_into_pac(&mut forest);
    group.bench_with_input("PAC Compile time", &forest, |b, forest| {
        b.iter(|| {
            forest
                .iter_matching([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    group.finish();
}

fn load_into<P: Forest4<usize>>(forest: &mut P) {
    const MAX: usize = 5000;
    for s in 1..=MAX {
        for p in 1..=MAX {
            if s * p < MAX {
                forest.insert(&[s, p, s * p, p % 2]);
            }
        }
    }
}


fn load_into_pac<P: QuadForestProfile<Identifier = usize>>(forest: &mut QuadForest<P>) {
    const MAX: usize = 5000;
    for s in 1..=MAX {
        for p in 1..=MAX {
            if s * p < MAX {
                forest.insert([s, p, s * p, p % 2]);
            }
        }
    }
}

criterion_group!(benches, search_prebuilt, search_lazy, load_greedy, load_lazy);
//criterion_group!(benches, load_lazy); // strange: load_lazy is much faster when it is the only benchmark...
criterion_main!(benches);
