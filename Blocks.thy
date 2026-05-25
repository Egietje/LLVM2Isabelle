theory Blocks
  imports "Instructions"
begin

section "Multiple blocks"

partial_function (tailrec) execute_blocks :: "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> llvm_labeled_blocks \<Rightarrow> state \<Rightarrow> (state * llvm_value option) result" where
  "execute_blocks prev label blocks state =
    (case map_of blocks label of
      None \<Rightarrow> err unknown_label
    | Some block \<Rightarrow>
      (case execute_block prev block state of
        err e \<Rightarrow> err e
      | ok (s', br) \<Rightarrow>
        (case br of
          return_value v \<Rightarrow> ok (s', Some v)
        | branch_label l \<Rightarrow> execute_blocks (Some label) l blocks s'
        )
      )
    )"

lemmas [code] = execute_blocks.simps

fun execute_function :: "llvm_function \<Rightarrow> state \<Rightarrow> (state * llvm_value option) result" where
  "execute_function (func _ ((l,b)#ls)) s = execute_blocks None l ((l,b)#ls) s"
| "execute_function _ s = ok (s, None)"

end