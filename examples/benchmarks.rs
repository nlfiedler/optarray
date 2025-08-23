//
// Copyright (c) 2025 Nathan Fiedler
//
use optarray::OptimalArray;
use std::time::Instant;

//
// This example was intended to show that the optimal array will grow in less
// time than a vector, however in practice that is not the case.
//

fn create_optarray(size: u64) {
    let start = Instant::now();
    let mut coll: OptimalArray<u64> = OptimalArray::new();
    for value in 0..size {
        coll.push(value);
    }
    let duration = start.elapsed();
    println!("optarray: {:?}", duration);
}

fn create_vector(size: u64) {
    let start = Instant::now();
    let mut coll: Vec<u64> = Vec::new();
    for value in 0..size {
        coll.push(value);
    }
    let duration = start.elapsed();
    println!("vector: {:?}", duration);
}

fn main() {
    println!("creating OptimalArray...");
    create_optarray(100_000_000);
    println!("creating Vec...");
    create_vector(100_000_000);
}
