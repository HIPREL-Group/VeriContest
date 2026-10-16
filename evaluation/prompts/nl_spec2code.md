# Instruction

You are an expert in Verus. You will be provided with a natural language problem description and a Verus specification. Your task is to generate the Rust code from them.

# Example

## Input

Write a function in Rust to check if each element of second sequence is smaller than its corresponding element in the first sequence.

Constraints:
- $arr1.length == arr2.length$

Starter Code:
```rust
impl Solution {
    pub fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> bool {
        
    }
}
```

Verus specification:
```rust
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
        requires
            arr1.len() == arr2.len(),
        ensures
            result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
    {
    }
}

}
```

## Output

```rust
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
        requires
            arr1.len() == arr2.len(),
        ensures
            result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
    {
        let mut index = 0;
        while index < arr1.len()
        {
            if arr1[index] <= arr2[index] {
                return false;
            }
            index += 1;
        }
        true
    }
}

}
```

# Input Field

## Problem Description

```
{{problem_description}}
```

## Verus Specification

```rust
{{verus_spec}}
```

# Output Field

Output a Verus program. Your answer should only contain a Verus program along with the specification as follows (you must quote the program in **```rust** for further automation):

```rust
{{Verus program}}
```

**CRITICAL REQUIREMENTS:**

- **Generate only Rust code. Do not include any Verus proofs.**

- **The code should be written in a Verus-verifiable format.**

- **Do not include explanations, analysis, markdown outside the Rust code fence, or multiple alternative programs.**

- **Ensure the code is efficient and avoids timeouts.**
