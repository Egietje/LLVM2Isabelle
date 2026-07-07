theory Syntax
  imports Definitions
begin

nonterminal llvm_id_node


syntax
  "_llvm_id_id"   :: "id \<Rightarrow> llvm_id_node"        ("_")
  "_llvm_id_num"  :: "num_token \<Rightarrow> llvm_id_node" ("_")
  "_llvm_local_id"  :: "llvm_id_node \<Rightarrow> llvm_identifier"
  "_llvm_global_id" :: "llvm_id_node \<Rightarrow> llvm_identifier"

ML \<open>
  val (llvm_syntax_active, setup_llvm_syntax_active) = 
    Attrib.config_bool @{binding llvm_syntax_active} (K false)
\<close>
setup \<open>setup_llvm_syntax_active\<close>

parse_translation \<open>
  let
    fun llvm_id_tr const ctxt [t] =
          let
            val name =
              case t of
                Const (@{syntax_const "_llvm_id_id"}, _) $ Free (s, _) => s
              | Const (@{syntax_const "_llvm_id_num"}, _) $ Free (s, _) => s
              | _ => raise TERM ("llvm_id_tr: unexpected layout", [t])
          in
            Const (const, dummyT) $ HOLogic.mk_string name
          end
      | llvm_id_tr const ctxt ts = raise TERM ("llvm_id_tr", ts)
  in
    [(@{syntax_const "_llvm_local_id"}, llvm_id_tr @{const_name lid}),
     (@{syntax_const "_llvm_global_id"}, llvm_id_tr @{const_name gid})]
  end
\<close>

print_translation \<open>
  let
    fun auto_normalize (Const (c, T)) =
          let val base = Long_Name.base_name c in 
            if base = "Cons" then Const (@{const_name List.list.Cons}, T)
            else if base = "Nil" then Const (@{const_name List.list.Nil}, T)
            else if base = "Char" then Const (@{const_name String.char.Char}, T)
            else if base = "True" then Const (@{const_name HOL.True}, T)
            else if base = "False" then Const (@{const_name HOL.False}, T)
            else Const (c, T)
          end
      | auto_normalize (f $ x) = auto_normalize f $ auto_normalize x
      | auto_normalize t = t;

    fun id_tr' syntax_const ctxt [hol_string] =
          if Config.get ctxt llvm_syntax_active then
            let
              val clean_term = auto_normalize hol_string
              val name = HOLogic.dest_string clean_term handle TERM _ => "unknown"
            in
              if name = "unknown" then
                raise Match
              else
                (* FIXED: Plain Syntax.const without Lexicon.mark_syntax wrapper *)
                (* This allows the bundle's mixfix engine to intercept it natively *)
                Syntax.const syntax_const $ 
                  (Syntax.const @{syntax_const "_llvm_id_id"} $ Syntax.free name)
            end
          else
            raise Match
            
      | id_tr' _ _ ts = raise Match
  in
    [(@{const_syntax lid}, id_tr' "_llvm_local_id"),
     (@{const_syntax gid}, id_tr' "_llvm_global_id")]
  end
\<close>

nonterminal phi_pair and phi_pairs
nonterminal call_arg and call_args
nonterminal llvm_add_flag

consts dummy_empty :: unit

print_translation \<open>
  let
    fun tr _ [Const (@{const_name "Definitions.add_default"}, _)] = 
          Syntax.const @{const_name dummy_empty}
      | tr _ _ = raise Match
  in
    [(@{const_name "Definitions.add_default"}, tr)]
  end
\<close>

bundle llvm_syntax
begin
  (* --- Core Types --- *)
  notation i1 ("i1")
  notation i32 ("i32")
  notation i64 ("i64")
  notation addr_type ("ptr")

  (* --- ICMP Condition Keywords --- *)
  notation comp_eq ("eq")
  notation comp_ne ("ne")
  notation comp_ugt ("ugt")
  notation comp_uge ("uge")
  notation comp_ult ("ult")
  notation comp_ule ("ule")
  notation comp_sgt ("sgt")
  notation comp_sge ("sge")
  notation comp_slt ("slt")
  notation comp_sle ("sle")

  (* --- Identifiers --- *)
  syntax
    "_llvm_local_id"  :: "llvm_id_node \<Rightarrow> llvm_identifier" ("%_")
    "_llvm_global_id" :: "llvm_id_node \<Rightarrow> llvm_identifier" ("@_")
    "_add_flag_nuw" :: "llvm_add_flag" ("nuw")
    "_add_flag_nsw" :: "llvm_add_flag" ("nsw")
    "_add_flag_both" :: "llvm_add_flag" ("nuw nsw")


  translations
    "_add_flag_nuw"  => "Definitions.add_nuw"
    "_add_flag_nsw"  => "Definitions.add_nsw"
    "_add_flag_both" => "Definitions.add_nuw_nsw"


  declare [[llvm_syntax_active = true]]

  (* --- Core Instruction Syntax --- *)
  syntax
    "_syntax_phi"    :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> (llvm_value_ref \<times> llvm_identifier) list \<Rightarrow> llvm_phi_node" 
      ("_ = 'phi _ _")

    "_syntax_alloca"       :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> llvm_instruction" ("_ = 'alloca _")
    "_syntax_alloca_align" :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> llvm_instruction" ("_ = 'alloca _ , 'align _")
    
    "_syntax_store"        :: "llvm_type \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> llvm_instruction" ("'store _ _ , _")
    "_syntax_store_align"  :: "llvm_type \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> int \<Rightarrow> llvm_instruction" ("'store _ _ , _ , 'align _")
    
    "_syntax_load"         :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> llvm_pointer \<Rightarrow> llvm_instruction" ("_ = 'load _ , _")
    "_syntax_load_align"   :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> llvm_pointer \<Rightarrow> int \<Rightarrow> llvm_instruction" ("_ = 'load _ , _ , 'align _")

    "_syntax_add" :: "llvm_identifier \<Rightarrow> llvm_add_flag \<Rightarrow> llvm_type \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_instruction" 
      ("_ = 'add _ _ _ , _" [0, 0, 0, 0, 0] 1000)
    "_syntax_add_default" :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_instruction" 
      ("_ = 'add _ _ , _" [0, 0, 0, 0] 1000)
      
    "_syntax_icmp"         :: "llvm_identifier \<Rightarrow> bool \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_type \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_instruction" 
      ("_ = 'icmp _ _ _ _ , _")

    "_syntax_call"         :: "llvm_type \<Rightarrow> llvm_identifier \<Rightarrow> (llvm_type \<times> llvm_value_ref) list \<Rightarrow> llvm_instruction" 
      ("'call _ _ _")
    "_syntax_call_assign"  :: "llvm_identifier \<Rightarrow> llvm_type \<Rightarrow> llvm_identifier \<Rightarrow> (llvm_type \<times> llvm_value_ref) list \<Rightarrow> llvm_instruction" 
      ("_ = 'call _ _ _")

    (* Terminators *)
    "_syntax_ret_void" :: "llvm_terminator_instruction" ("'ret 'void")
    "_syntax_ret"      :: "llvm_type \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_terminator_instruction" ("'ret _ _")
    "_syntax_br_i1"    :: "llvm_value_ref \<Rightarrow> llvm_identifier \<Rightarrow> llvm_identifier \<Rightarrow> llvm_terminator_instruction" ("'br 'i1 _ , 'label _ , 'label _")
    "_syntax_br_label" :: "llvm_identifier \<Rightarrow> llvm_terminator_instruction" ("'br 'label _")

  (* --- Terminating Translation Layer --- *)
  translations
    "_syntax_phi v t ps"          => "Definitions.phi v t ps"
    
    "_syntax_alloca v t"          => "Definitions.alloca v t Option.None"
    "_syntax_alloca_align v t a"  => "Definitions.alloca v t (Option.Some a)"
    
    "_syntax_store t v p"         => "Definitions.store t v p Option.None"
    "_syntax_store_align t v p a" => "Definitions.store t v p (Option.Some a)"
    
    "_syntax_load v t p"          => "Definitions.load v t p Option.None"
    "_syntax_load_align v t p a"  => "Definitions.load v t p (Option.Some a)"
    
    "_syntax_add v f t o1 o2" => "Definitions.add v f t o1 o2"
    "_syntax_add_default v t o1 o2" => "Definitions.add v Definitions.add_default t o1 o2"
    "_syntax_icmp v s c t o1 o2"  => "Definitions.icmp v s c t o1 o2"
    
    "_syntax_call t f as"         => "Definitions.call Option.None t f as"
    "_syntax_call_assign v t f as" => "Definitions.call (Option.Some v) t f as"

    "_syntax_ret_void"      => "Definitions.ret Option.None"
    "_syntax_ret t v"       => "Definitions.ret (Option.Some (t, v))"
    "_syntax_br_i1 c l1 l2" => "Definitions.br_i1 c l1 l2"
    "_syntax_br_label l"    => "Definitions.br_label l"

  
end

term "add (lid ''sub'') add_nsw i32 (reg (lid ''1'')) (val (vi32 (-1)))"


context
  includes llvm_syntax
begin


term "%2"
term "%tmp1 = add i32 (reg %res), (reg %val1)"  



definition "example_llvm_block \<equiv> [
  (%ptr = alloca i32, align 4),
  
  (%val1 = load i32, %ptr),
  
  %val2 = add nuw i32 %val1, 42,
  
  %cond = icmp eq sge i32 %val2, 100,
  
  store i32 %val2, %ptr, align 4,
  
  %call_res = call i32 @external_fn(i32 %val2, i32 0)
]"

definition "example_phi_loop \<equiv> 
%merge = phi i32 [(%entry_block, (reg %val1)), (%loop_backtrack, (reg %val2))]
"

definition "example_terminators \<equiv> [
  br i1 (reg %cond), label %true_exit, label %false_exit,
  
  br label %loop_merge,
  
  ret i32 (reg %val2)
]"

end

end