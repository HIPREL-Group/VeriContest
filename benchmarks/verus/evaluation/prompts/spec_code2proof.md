# Instruction

You are an expert in Verus. You will be provided with a Verus specification along with the executable Rust code. Your task is to generate the Verus proofs to verify this program.

# Example

## Input

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
            invariant
                0 <= index <= arr1.len(),
                arr1.len() == arr2.len(),
                0 <= index <= arr2.len(),
                forall|k: int| 0 <= k < index ==> arr1[k] > arr2[k],
            decreases arr1.len() - index,
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

```rust
{{verus_program}}
```

# Output Field

Output a verified Verus program with proofs. Your answer should only contain a verified Verus program as follows (you must quote the program in **```rust** for further automation):

```rust
{{Verus program}}
```

**CRITICAL REQUIREMENTS:**

- **Preserve the original executable Rust code and specification.**

- **Do not include explanations, analysis, markdown outside the Rust code fence, or multiple alternative programs.**
