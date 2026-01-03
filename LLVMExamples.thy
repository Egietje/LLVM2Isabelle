theory LLVMExamples
  imports LLVM
begin

section "Simple Branching"

definition sbmain :: "llvm_instruction_block" where
  "sbmain = ([
    alloca ''%1'' i32 (Some 4),
    alloca ''%2'' i32 (Some 4),
    alloca ''%3'' i32 (Some 4),
    alloca ''%4'' i32 (Some 4),
    alloca ''%5'' i32 (Some 4),
    store i32 (val (vi32 0)) (ptr (reg ''%1'')) (Some 4),
    store i32 (val (vi32 1)) (ptr (reg ''%2'')) (Some 4),
    store i32 (val (vi32 2)) (ptr (reg ''%3'')) (Some 4),
    load ''%6'' i32 (ptr (reg ''%2'')) (Some 4),
    add ''%7'' add_nsw i32 (reg ''%6'') (val (vi32 1)),
    load ''%8'' i32 (ptr (reg ''%3'')) (Some 4),
    icmp ''%9'' False comp_eq i32 (reg ''%7'') (reg ''%8'')],
    br_i1 (reg ''%9'') ''10'' ''12''
  )"

definition sb10 :: "llvm_instruction_block" where
  "sb10 = ([
    store i32 (val (vi32 3)) (ptr (reg ''%4'')) (Some 4),
    load ''%11'' i32 (ptr (reg ''%4'')) (Some 4),
    store i32 (reg ''%11'') (ptr (reg ''%3'')) (Some 4)],
    br_label ''14''
  )"

definition sb12 :: "llvm_instruction_block" where
  "sb12 = ([
    store i32 (val (vi32 4)) (ptr (reg ''%5'')) (Some 4),
    load ''%13'' i32 (ptr (reg ''%5'')) (Some 4),
    store i32 (reg ''%13'') (ptr (reg ''%3'')) (Some 4)],
    br_label ''14''
  )"

definition sb14 :: "llvm_instruction_block" where
  "sb14 = ([
    load ''%15'' i32 (ptr (reg ''%3'')) (Some 4)],
    ret i32 (reg ''%15'')
  )"

definition simple_branching_main :: "llvm_function" where
  "simple_branching_main = func (func_def ''main'' i32) sbmain (Mapping.of_alist [(''10'', sb10), (''12'', sb12), (''14'', sb14)])"

(*
int main() {
    int y = 1;
    int x = y?1:0;
    return x;
}
*)
(*
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  %5 = load i32, ptr %2, align 4
  %6 = icmp ne i32 %5, 0
  br i1 %6, label %7, label %9

7:
  store i32 1, ptr %4, align 4
  %8 = load i32, ptr %4, align 4
  br label %10

9:
  br label %10

10:
  %11 = phi i32 [ %8, %9 ], [ 0, %9 ]
  store i32 %11, ptr %3, align 4
  %12 = load i32, ptr %3, align 4
  ret i32 %12
}
*)
                         
lemma "wp_never_err (execute_function empty_state simple_branching_main) (\<lambda>ret. True)"
  unfolding empty_state_def simple_branching_main_def sbmain_def sb10_def sb12_def sb14_def 
  apply (simp add: execute_blocks.simps)
  apply (intro wp_intro)
  by eval

(* apply (auto simp add: empty_state_def simple_branching_main_def sbmain_def sb10_def sb12_def sb14_def execute_blocks.simps) *)
(* DISCUSS: what kinda lemmas/simps am I missing? *)

value "execute_function empty_state simple_branching_main"



section "Phi Node"

definition pmain :: "llvm_instruction_block" where
  "pmain = ([
    alloca ''1'' i32 (Some 4),
    alloca ''2'' i32 (Some 4),
    alloca ''3'' i32 (Some 4),
    alloca ''4'' i32 (Some 4),
    store i32 (val (vi32 0)) (ptr (reg ''1'')) (Some 4),
    store i32 (val (vi32 1)) (ptr (reg ''2'')) (Some 4),
    load ''5'' i32 (ptr (reg ''2'')) (Some 4),
    icmp ''6'' False comp_ne i32 (reg ''5'') (val (vi32 0))],
    br_i1 (reg ''6'') ''7'' ''9''
  )"

definition p7 :: "llvm_instruction_block" where
  "p7 = ([
    store i32 (val (vi32 1)) (ptr (reg ''4'')) (Some 4),
    load ''8'' i32 (ptr (reg ''4'')) (Some 4)],
    br_label ''10''
  )"

definition p9 :: "llvm_instruction_block" where
  "p9 = ([],
    br_label ''10''
  )"

definition p10 :: "llvm_instruction_block" where
  "p10 = ([
    phi ''11'' i32 [(''7'', reg ''8''), (''9'', val (vi32 0))],
    store i32 (reg ''11'') (ptr (reg ''3'')) (Some 4),
    load ''12'' i32 (ptr (reg ''3'')) (Some 4)],
    ret i32 (reg ''12'')
  )"

definition phi_main :: "llvm_function" where
  "phi_main = func (func_def ''main'' i32) pmain (Mapping.of_alist [(''7'', p7), (''9'', p9), (''10'', p10)])"
(*
int main() {
    int y = 1;
    int x = y?1:0;
    return x;
}

define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  %5 = load i32, ptr %2, align 4
  %6 = icmp ne i32 %5, 0
  br i1 %6, label %7, label %9

7:
  store i32 1, ptr %4, align 4
  %8 = load i32, ptr %4, align 4
  br label %10

9:
  br label %10

10:
  %11 = phi i32 [ %8, %9 ], [ 0, %9 ]
  store i32 %11, ptr %3, align 4
  %12 = load i32, ptr %3, align 4
  ret i32 %12
}
*)

value "execute_function (empty_register_model, empty_memory_model, empty_memory_model) phi_main"

end