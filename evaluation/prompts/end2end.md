# Instruction

You are an expert in Verus. You will be provided with a natural language problem description. Your task is to generate a verified Verus program from the problem description, including the Verus specification, executable Rust code, and the corresponding Verus proofs.

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

```
{{problem_description}}
```

# Output Field

Output a verified Verus program. Your answer should only contain a Verus program (you must quote the program in **```rust** for further automation):

```rust
{{Verified Verus program}}
```

**CRITICAL REQUIREMENTS:**

- **Ensure the code is efficient and avoids timeouts.**

- **Generate the Verus specification, executable Rust code, and the corresponding Verus proofs together.**

- **Do not include explanations, analysis, markdown outside the Rust code fence, or multiple alternative programs.**
