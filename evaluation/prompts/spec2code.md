# Instruction

You are an expert in Verus. You will be provided with a Verus specification. Your task is to generate the Rust code that aligns with the specification.

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

```
{{verus_spec}}
```

# Output Field

Output a Verus program with the specification. Your answer should only contain a Verus program as follows (you must quote the program in **```rust** for further automation):

```rust
{{Verus program with the specification}}
```

**CRITICAL REQUIREMENTS:**

- **Generate only Rust code. Do not include any proofs.**

- **Ensure the code is efficient and avoids timeouts.**

- **The code should be written in a Verus-verifiable format.**

- **Do not include explanations, analysis, markdown outside the Rust code fence, or multiple alternative programs.**
