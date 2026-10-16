# Instruction

You are an expert in Verus. You will be provided with a natural language problem description. Your task is to generate the Verus specification from the problem description.

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
    }
}

}
```

# Input Field

```
{{problem_description}}
```

# Output Field

Output a Verus specification. Your answer should only contain a Verus program with only the specification as follows (you must quote the program in **```rust** for further automation):

```rust
{{Verus program containing only the specification}}
```

**CRITICAL REQUIREMENTS:**

- **Generate only Verus specification. Do not include any code or proofs.**

- **Do not include explanations, analysis, markdown outside the Rust code fence, or multiple alternative programs.**
