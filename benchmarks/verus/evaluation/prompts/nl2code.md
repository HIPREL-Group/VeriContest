# Instruction

You are an expert in Rust. You will be provided with a natural language problem description. Your task is to generate the Rust code from the problem description.

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
impl Solution {
    pub fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> bool {
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
```

# Input Field

```
{{problem_description}}
```

# Output Field

Output a Rust program. Your answer should only contain a Rust program (you must quote the program in **```rust** for further automation):

```rust
{{Rust program}}
```

**CRITICAL REQUIREMENTS:**

- **The code should be written in a Verus-verifiable format.**

- **Ensure the code is efficient and avoids timeouts.**

- **Do not include explanations, analysis, markdown outside the Rust code fence, or multiple alternative programs.**
