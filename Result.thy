theory Result
  imports "HOL-Library.Monad_Syntax"
begin


datatype error = unknown_register | uninitialized_register | register_override
  | unallocated_address | uninitialized_address
  | not_an_address | incompatible_types | unknown_label

datatype 'a result = ok 'a | err error


definition bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind R f = (case R of err e \<Rightarrow> err e | ok x \<Rightarrow> f x)"

definition return :: "'a \<Rightarrow> 'a result" where
  "return x = ok x"

adhoc_overloading
  Monad_Syntax.bind==bind
(* TODO Monad laws *)


end