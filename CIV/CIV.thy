header {* A List-Machine Benchmark for Mechanized Metatheory (in Isabelle) *}

theory CIV
imports Main
begin

(* ---------------------------------------------------------
 * 
 * Syntax
 *
 * ---------------------------------------------------------
 *)


types V    = nat                        (* Variables *)
      L    = nat                        (* Labels *)
datatype F = Fst | Snd                  (* Field selectors *)


(* Code blocks *)
datatype I = Cons V V V                 (* Allocate a cons cell *)
           | FetchField V F V           (* Access the field of a cons cell *)

           | BranchIfNil V L            (* Conditional jump *)
           | Jump L                     (* Unconditional jump *)

           | Halt                       (* Stop execution *)
           | Seq I I   (infixr "\<guillemotright>" 60)  (* Sequential execution *)


(* Programs *)
types P    = "L \<rightharpoonup> I"



(* Examples *)

constdefs sample :: "P"
"sample \<equiv> [ 0 \<mapsto> Cons 0 0 1 
              \<guillemotright> Cons 0 1 1 
              \<guillemotright> Cons 0 1 1 
              \<guillemotright> Jump 1 
          , 1 \<mapsto> BranchIfNil 1 2 
              \<guillemotright> FetchField 1 Fst 1 
              \<guillemotright> BranchIfNil 0 1
              \<guillemotright> Jump 2 
          , 2 \<mapsto> Halt 
          ]"

constdefs sampleLoop :: P
"sampleLoop \<equiv> [ 0 \<mapsto> Jump 0 ]"



(* ----------------------------------------------- 
 *
 * Operational Semantics 
 *
 * ----------------------------------------------- 
 *)


(* Values *)
datatype A = Null                  (* Nil cell *)
           | Node A A              (* Cons cell *)


(* 
Machine States

The machine state has two components:
 - a store, which maps variable names to values, and
 - an instruction pointer, which specifies what to do next.

*)

types R    = "V \<rightharpoonup> A"   (* The type of stores *)
      S    = "R \<times> I"   (* The type of machine states *)


(* A small-step operational semantics:

- The relation 'step' relates machine states.
- Two states are related if the machine can transition between them.
- The relation is inductively defined.
- Decisions are based on the instruction pointer.
 
*)

consts step :: "P \<Rightarrow> (S\<times>S) set"
inductive "step p"
intros 

Seq[intro!]:
"((r, (i1\<guillemotright>i2)\<guillemotright>i3)
 ,(r, i1\<guillemotright>(i2\<guillemotright>i3))) \<in> step p"

Fetch[intro!]:
"\<lbrakk> r v = Some (Node a0 a1) \<rbrakk> \<Longrightarrow> 
 ((r, FetchField v f v' \<guillemotright> i)
 ,(r(v' \<mapsto> if f = Fst then a0 else a1), i)) \<in> step p"

Cons[intro!]: 
"\<lbrakk> r v0 = Some a0; r v1 = Some a1 \<rbrakk> \<Longrightarrow>
 ((r, Cons v0 v1 v' \<guillemotright> i)
 ,(r (v' \<mapsto> Node a0 a1), i)) \<in> step p"

BranchNot: 
"\<lbrakk> r v = Some (Node a0 a1) \<rbrakk> \<Longrightarrow>
 ((r, BranchIfNil v l \<guillemotright> i)
 ,(r, i)) \<in> step p" 

BranchYes: 
"\<lbrakk> r v = Some Null; p l = Some i' \<rbrakk> \<Longrightarrow>
 ((r, BranchIfNil v l \<guillemotright> i)
 ,(r, i')) \<in> step p" 

Jump[intro!]: 
"\<lbrakk> p l = Some i' \<rbrakk> \<Longrightarrow>
 ((r, Jump l)
 ,(r, i')) \<in> step p"



(* -----------------------------------------------------------
 * 
 * What constitutes a "good" program?
 *
 * ----------------------------------------------------------- 
 *)


(* The machine is in a good state if either:
   - it can continue executing, or
   - the program execution has terminated.
 *)
   
thm step.induct

consts goodState :: "P \<Rightarrow> S set"
coinductive "goodState p"
intros
step: "\<lbrakk> (s1,s2) \<in> step p; s2 \<in> goodState p \<rbrakk> \<Longrightarrow> s1 \<in> goodState p"
halt[intro!]: "(r,Halt) \<in> goodState p"


(* Note: 
   The set 'goodState' is "coinductive" because we are interested 
   in the largest set that satisifes the two properties above.
   In particular, this includes programs that may run forever. 
 *)


(* We say that a program 'runs' if:
   - it has a valid entry point (label 0, think "main" in a C program)
   - its initial state is "good"

   Note: upon start, a program has Null in register 0.
 *)

constdefs runs :: "P \<Rightarrow> bool"
"runs p \<equiv> case p 0 of 
            None \<Rightarrow> False |
            Some i \<Rightarrow> ([0\<mapsto>Null],i) \<in> goodState p"


(* Specialized rules that may be used aggresively
   (i.e., no need to backtrack) to conclude new facts.   
 *)
lemmas goodState_safe_irules [intro!] =
  goodState.step[OF step.Cons]
  goodState.step[OF step.Seq]
  goodState.step[OF step.Jump]
  goodState.step[OF step.Fetch]

lemmas goodState_irules [intro] =
  goodState.step[OF step.BranchYes]
  goodState.step[OF step.BranchNot]



(* Examples *)

lemma "runs sample"  
  apply (simp add: runs_def sample_def)
  apply (auto, rule goodState.step[OF step.BranchNot])
  apply (auto, rule goodState.step[OF step.BranchYes])
by auto

lemma "runs sampleLoop"
  apply (simp add: runs_def sampleLoop_def)
  apply (rule goodState.coinduct [where ?X = "{([0 \<mapsto> Null], Jump 0)}"])
  apply (auto, rule, rule, auto)
done



(* -------------------------------------------------------
 *
 * Type System
 *
 * -------------------------------------------------------
 *)

datatype T = TNil            (* The type of Null values *)
           | TCons T         (* The type of Cons values (of T) *)
           | TList T         (* The type of list (Nil or Cons) values of T *)



(* A subtyping relation on types *)

consts sub :: "(T \<times> T) set"
inductive sub
intros
nil_nil[intro!]:   "(TNil,TNil) \<in> sub"
nil_list[intro!]:  "(TNil,TList t) \<in> sub"
cons_cons[intro!]: "\<lbrakk> (t,t') \<in> sub \<rbrakk> \<Longrightarrow> (TCons t, TCons t') \<in> sub"
list_list[intro!]: "\<lbrakk> (t,t') \<in> sub \<rbrakk> \<Longrightarrow> (TList t, TList t') \<in> sub"
cons_list[intro!]: "\<lbrakk> (t,t') \<in> sub \<rbrakk> \<Longrightarrow> (TCons t, TList t') \<in> sub"



(* Inverted rules *)
inductive_cases sub_TNil[elim!]: "(t,TNil) \<in> sub"
inductive_cases sub_TCons[elim!]: "(t1,TCons t2) \<in> sub" 
inductive_cases sub_TList[elim!]: "(t1,TList t2) \<in> sub"
thm sub_TNil
thm sub_TCons

lemma sub_refl[intro!]: "(t,t) \<in> sub"
  by (induct t,auto)


    




(* Computing least upper boubds *)

consts lub :: "T \<Rightarrow> T \<Rightarrow> T"
primrec
"lub TNil x      = (case x of
                      TNil     \<Rightarrow> TNil |
                      TCons t1 \<Rightarrow> TList t1 | 
                      TList t1 \<Rightarrow> TList t1)"
"lub (TCons t) x = (case x of
                      TNil     \<Rightarrow> TList t | 
                      TCons t1 \<Rightarrow> TCons (lub t t1) | 
                      TList t1 \<Rightarrow> TList (lub t t1))"
"lub (TList t) x = (case x of
                      TNil     \<Rightarrow> TList t |
                      TCons t1 \<Rightarrow> TList (lub t t1) |
                      TList t1 \<Rightarrow> TList (lub t t1))"

lemma lub_ref[iff]: "lub t t = t"
  by (induct t, auto)



(* LUBs and sub-typing interact as expected. *)

lemma lub_sub_left[intro!]: "\<And>t2. (t1,lub t1 t2) \<in> sub" 
  apply (induct t1) by (case_tac t2, auto)+

lemma lub_sym: "\<And>t2. lub t1 t2 = lub t2 t1" 
  apply (induct t1) by (case_tac t2, auto)+
 
lemma lub_sub_right[intro!]: "(t2,lub t1 t2) \<in> sub"
  using lub_sym by (rule ssubst,fast)

lemma lub_least: " \<And>t1 t2. \<lbrakk> (t1,t4) \<in> sub; (t2,t4) \<in> sub \<rbrakk>
                   \<Longrightarrow> (lub t1 t2,t4) \<in> sub"
  by (induct t4,auto)



(* Typing environments 

- To type the store of the machine, we associate types with
  the different variables (registers).

- To type a program, we associate a store-type with each 
  program block.  The store type specifies the types of
  values that should be placed in the various registers
  before we can start executing the block.
*)

types E    = "V \<rightharpoonup> T"   (* Associates variables with types. *)
      PT   = "L \<rightharpoonup> E"   (* Associates labels with environments. *)


(* Examples *)

constdefs sampleT :: "PT"
"sampleT \<equiv> [ 0 \<mapsto> [0 \<mapsto> TNil]
           , 1 \<mapsto> [0 \<mapsto> TNil, 1 \<mapsto> TList TNil]
           , 2 \<mapsto> empty
           ]"

constdefs sampleLoopT :: "PT"
"sampleLoopT \<equiv> [ 0 \<mapsto> [0 \<mapsto> TNil ] ]"


(* We can "lift" the notion of sub-typing to environments *)
constdefs subEnv :: "E \<Rightarrow> E \<Rightarrow> bool"
"subEnv e1 e2 \<equiv> \<forall>x t. (e2 x = Some t) \<longrightarrow> (\<exists> s. (e1 x = Some s) \<and> (s,t) \<in> sub)"


(* This is the type of the initial environment. *)
constdefs initTEnv :: "E"
"initTEnv \<equiv> [ 0 \<mapsto> TNil ]"

declare initTEnv_def [simp]



(* Typing rules for single instructions:

Given the type of the whole program, we define a 
relation between instructions and environments:

E1 \<turnstile> I :: E2

E1: the types of variables before executing I
E2: the typpes of the variables after executing I

*)
 
consts checkInstr :: "PT \<Rightarrow> (E \<times> I \<times> E) set"
inductive "checkInstr p"
intros
Seq[intro!]:
"\<lbrakk> (e1,i1,e2) \<in> checkInstr p; (e2,i2,e3) \<in> checkInstr p \<rbrakk>
\<Longrightarrow>
(e1, i1 \<guillemotright> i2, e3) \<in> checkInstr p"

BranchIfNil_TList: 
"\<lbrakk> e v = Some (TList t); p l = Some e1; subEnv (e(v\<mapsto>TNil)) e1 \<rbrakk> 
\<Longrightarrow>
(e, BranchIfNil v l, e(v\<mapsto>TCons t)) \<in> checkInstr p"

BranchIfNil_TCons: 
"\<lbrakk> e v = Some (TCons t); p l = Some e1; subEnv (e(v\<mapsto>TNil)) e1 \<rbrakk> 
\<Longrightarrow>
(e,BranchIfNil v l,e) \<in> checkInstr p"

BranchIfNil_TNil:  
"\<lbrakk> e v = Some TNil; p l = Some e1; subEnv e e1 \<rbrakk> 
\<Longrightarrow>
(e,BranchIfNil v l,e) \<in> checkInstr p"

FetchField[intro!]: 
"\<lbrakk> e v = Some (TCons t) \<rbrakk> 
\<Longrightarrow>
(e,FetchField v F v',e(v'\<mapsto>if (F = Fst) then t else TList t)) \<in> checkInstr p"

Cons[intro!]: 
"\<lbrakk> e v0 = Some t0; e v1 = Some t1; lub (TList t0) t1 = TList t \<rbrakk> 
\<Longrightarrow>
(e,Cons v0 v1 v,e(v\<mapsto>TCons t)) \<in> checkInstr p"


(* Inverted rules *)
inductive_cases checkInstr_Seq: "(e1,i1\<guillemotright>i2,e2) \<in> checkInstr pt"
inductive_cases checkInstr_BranchIfNil: 
  "(e1,BranchIfNil v0 l,e2) \<in> checkInstr p"
inductive_cases checkInstr_FetchField: 
  "(e1,FetchField v0 f v,e2) \<in> checkInstr p"
inductive_cases checkInstr_Cons: "(e1,Cons v0 v1 v,e2) \<in> checkInstr pt"
inductive_cases checkInstr_Halt: "(e1,Halt,e2) \<in> checkInstr pt"
inductive_cases checkInstr_Jump: "(e1,Jump l,e2) \<in> checkInstr pt"

thm checkInstr_Seq
thm checkInstr_Jump  (* Jumps are impossible *)


(* Typing rules for program blocks:

E \<turnstile> I

asserts that in environment E, I is a well-typed block.
*)

consts checkBlock :: "PT \<Rightarrow> (E \<times> I) set"
inductive "checkBlock pt"
intros
Halt[intro!]: 
"(e,Halt) \<in> checkBlock pt"

Seq[intro!]:  
"\<lbrakk> (e,i1,e') \<in> checkInstr pt; (e',i2) \<in> checkBlock pt \<rbrakk> 
\<Longrightarrow> 
(e,i1\<guillemotright>i2) \<in> checkBlock pt"

Jump[intro!]: 
"\<lbrakk> pt l = Some e1; subEnv e e1 \<rbrakk> 
\<Longrightarrow> 
(e,Jump l) \<in> checkBlock pt"

(* Inverted rules *)
inductive_cases checkBlock_Seq[elim!]: "(e,i1\<guillemotright>i2) \<in> checkBlock pt"
inductive_cases checkBlock_Jump[elim!]: "(e,Jump l) \<in> checkBlock pt"
thm checkBlock_Jump



(* Typing rules for an entire progrm *)


(* Is given block in a program well typed? *)
constdefs checkBlockName :: "PT \<Rightarrow> P \<Rightarrow> L \<Rightarrow> bool"
"checkBlockName pt p l \<equiv> case pt l of
                           Some e \<Rightarrow> (case p l of
                                       Some i \<Rightarrow> (e,i) \<in> checkBlock pt |
                                       None   \<Rightarrow> False) |
                           None \<Rightarrow> True" 


(* A program is well-typed if all of its blocks are *)
constdefs checkProg :: "PT \<Rightarrow> P \<Rightarrow> bool"
"checkProg pt p \<equiv> (\<forall>l. checkBlockName pt p l) \<and> pt 0 = Some initTEnv"


(* Some facts about well-typed programs *)

(* All of their blocks are well-typed *)
lemma progOK_blocks: "checkProg pt p \<Longrightarrow> checkBlockName pt p l"
  using checkProg_def by simp

(* The type of the initial block is the initial environment *)
lemma progOK_entry: "checkProg pt p \<Longrightarrow> pt 0 = Some initTEnv"
  using checkProg_def by simp


(* All labels are defined, and point to well-typed blocks. *) 
lemma getCode:
  assumes A: "checkProg pt p"
      and B: "pt l = Some e"
  shows      "\<exists>i. p l = Some i \<and> (e,i) \<in> checkBlock pt"
proof -
  from A and progOK_blocks have "checkBlockName pt p l" by fast
  then obtain i where "p l = Some i" and "(e,i) \<in> checkBlock pt" 
     using A B checkBlockName_def by (cases "p l",simp_all)
  thus ?thesis by simp
qed



(* Examples *)


(* The sample program is type correct *)
lemma "checkProg sampleT sample"
proof -
  have Entry: "sampleT 0 = Some initTEnv" by (simp add: sampleT_def)

  have block0: "([0 \<mapsto> TNil], 
                  Cons 0 0 1 
                \<guillemotright> Cons 0 1 1 
                \<guillemotright> Cons 0 1 1 
                \<guillemotright> Jump 1) \<in> checkBlock sampleT" 
    by (auto simp:sampleT_def subEnv_def)

  have block1: "([0 \<mapsto> TNil, 1 \<mapsto> TList TNil],
                 BranchIfNil 1 2 
               \<guillemotright> FetchField 1 Fst 1 
               \<guillemotright> BranchIfNil 0 1
               \<guillemotright> Jump 2) \<in> checkBlock sampleT"
   apply (rule checkBlock.Seq [OF checkInstr.BranchIfNil_TList])
   apply (auto simp: sampleT_def subEnv_def) 
   apply (rule checkInstr.BranchIfNil_TNil) 
   by (auto simp: subEnv_def)

  have block2: "(empty,Halt) \<in> checkBlock sampleT" 
    by (rule checkBlock.Halt)
   
  have no_more: "\<And>l. l > 2 \<Longrightarrow> checkBlockName sampleT sample l"
    by (simp add: checkBlockName_def sampleT_def)

  have Blocks: "\<forall>l. checkBlockName sampleT sample l"
  proof 
    fix l show "checkBlockName sampleT sample l"
    proof (cases l)
    case 0 from block0 show ?thesis using prems 
      by (auto simp: checkBlockName_def sampleT_def sample_def) next
    case (Suc n) thus ?thesis
      proof (cases n)
      case 0 from block1 show ?thesis using prems 
        by (auto simp: checkBlockName_def sampleT_def sample_def) next
      case (Suc m) thus ?thesis
        proof (cases m)
        case 0 from block2 show ?thesis using prems 
          by (auto simp: checkBlockName_def sampleT_def sample_def) next
        case (Suc m') from no_more show ?thesis using prems by simp
        qed
      qed
    qed
  qed

  from Blocks and Entry show ?thesis
    by (simp add: checkProg_def)
qed


(* The looping sample program is type correct *)
lemma "checkProg sampleLoopT sampleLoop"
proof -
  have B0: "(initTEnv,Jump 0) \<in> checkBlock sampleLoopT"
    apply (simp add: checkProg_def sampleLoop_def)
    apply (rule checkBlock.Jump)
    apply (auto simp: subEnv_def sampleLoopT_def)
  done
  have "\<forall>l. checkBlockName sampleLoopT sampleLoop l"
  proof 
    fix l show "checkBlockName sampleLoopT sampleLoop l"
    using B0 by (cases l, simp_all add: checkBlockName_def 
                                        sampleLoopT_def sampleLoop_def)
  qed
  thus ?thesis by (simp add: checkProg_def sampleLoopT_def sampleLoop_def)
qed





(* Typing Values 

The definitions bellow associates types with values.
This is another way of saying that we are defining
the semantics of types (i.e., for each type we define
the set of values that belong to it.)
*)

consts valType :: "(A\<times>T) set"
inductive valType
intros
Tip_TNil   [intro!]: "(Null,TNil) \<in> valType"
Tip_TList  [intro!]: "(Null,TList t) \<in> valType"
Node_TCons [intro!]: "\<lbrakk> (x,t) \<in> valType; (xs,TList t) \<in> valType \<rbrakk> 
                    \<Longrightarrow> (Node x xs, TCons t) \<in> valType"
Node_TList [intro!]: "\<lbrakk> (x,t) \<in> valType; (xs,TList t) \<in> valType \<rbrakk>
                    \<Longrightarrow> (Node x xs, TList t) \<in> valType"

(* Inverted rules *)
inductive_cases Node_TCons[elim!]: "(Node x xs,TCons t) \<in> valType"
inductive_cases Node_TList[elim!]: "(Node x xs,TList t) \<in> valType"
inductive_cases Null_T[elim!]: "(Null,t) \<in> valType"
inductive_cases Val_TNil[elim!]: "(x,TNil) \<in> valType"
inductive_cases Val_TCons[elim!]: "(x,TCons t) \<in> valType"

inductive_cases Val_TList: "(x,TList t) \<in> valType"
inductive_cases Node_T: "(Node x xs,t) \<in> valType"
thm Node_TCons




(* Well-typed stores:
   A store is typed by an environment if the values
   in the registers match their corresponding types. 
 *)
constdefs envType :: "R \<Rightarrow> E \<Rightarrow> bool"
"envType r e \<equiv> \<forall>x. (case e x of
                      Some t \<Rightarrow> (case r x of
                                  Some v \<Rightarrow> (v,t) \<in> valType |
                                  None \<Rightarrow> False) |
                      None \<Rightarrow> True)"


(* A convenient way to prove that a store is well-typed. *)
lemma envTypeI:
 assumes A: "\<And>x t. \<lbrakk> e x = Some t \<rbrakk> \<Longrightarrow> \<exists>v. r x = Some v \<and> (v,t) \<in> valType"
 shows      "envType r e"
 apply (unfold envType_def,rule, case_tac "e x",simp_all)
 apply (drule A, erule exE, simp)
done


(* Lookup a value in a well-typed store.
   Produces a well-typed value. *)
lemma getVar:
  assumes A: "envType r e"
      and B: "e x = Some t"
  shows      "\<exists>v. r x = Some v \<and> (v,t) \<in> valType"
proof -
  from prems obtain v where "r x = Some v"
                        and "(v,t) \<in> valType"
    apply (simp add:envType_def)
    apply (erule_tac x ="x" in allE, simp)
    apply (cases "r x", simp_all)
  done
  thus ?thesis by simp
qed


(* Cast between subtypes:
If a value, V, is of type T, which happens to be a subtype of S,
then V also has type S.
 *)
lemma cast: "\<And>t1 t2. \<lbrakk> (v,t1) \<in> valType; (t1,t2) \<in> sub \<rbrakk> \<Longrightarrow> (v,t2) \<in> valType"
proof (induct v)
  case Null thus ?case by (cases t2,auto) next
  case (Node x xs) thus ?case by (cases t2,fast+)
qed


(* Cast between environments with subtype types *)
lemma castEnv:
  assumes A: "envType r e1"
      and B: "subEnv e1 e2"
  shows      "envType r e2"
proof (rule envTypeI)
  fix x t assume "e2 x = Some t"
  with B subEnv_def have "\<exists>t1. e1 x = Some t1 \<and> (t1,t) \<in> sub" by simp
  then obtain t1 where C: "e1 x = Some t1" and D: "(t1,t) \<in> sub" by fast
  from A C obtain v where E: "r x = Some v" 
                      and F: "(v,t1) \<in> valType" using getVar by fast
  from F D have "(v,t) \<in> valType" using cast by fast
  with E show "\<exists>v. r x = Some v \<and> (v,t) \<in> valType" by simp
qed


(* The set of well-typed states for a program *)
constdefs TypedState :: "PT \<Rightarrow> S set"
"TypedState pt \<equiv> { (r,i). \<exists>e. envType r e \<and> (e,i) \<in> checkBlock pt }"

declare TypedState_def[simp]



(* ------------------------------------------------------------
 * 
 * Proving soundness
 *
 * ------------------------------------------------------------
 *)



(* Assertion that well typed instructions can step (or are halted)
   and they result in well typed states. *)

constdefs steps :: "PT \<Rightarrow> P \<Rightarrow> R \<Rightarrow> I \<Rightarrow> bool"
"steps pt p r i \<equiv> \<exists>s. ((r,i),s) \<in> step p \<and> s \<in> TypedState pt \<union> goodState p"

declare steps_def[simp]


(* Jump instructions are OK *)
lemma Jump_steps:
assumes progOK:    "checkProg pt p"
    and envOK:     "envType r e"
    and labelOK:   "pt l = Some e1"
    and targetSub: "subEnv e e1"
shows "steps pt p r (Jump l)" 
proof -
  from progOK and labelOK 
    obtain i1 where targetCode: "p l = Some i1" 
                and targetEnv:  "(e1,i1) \<in> checkBlock pt" using getCode by fast
  from targetCode have Step: "((r,Jump l),(r,i1)) \<in> step p" by (rule step.Jump)

  from envOK and targetSub 
    have targetEnvOK: "envType r e1" using castEnv by fast
  with targetEnv have "(r,i1) \<in> TypedState pt" by auto
  with Step show ?thesis by auto
qed


(* Updating a well-type env. with a well-typed value
   results in a well-typed environment. *)
lemma updEnv:
assumes envOK: "envType r e"
    and valOK: "(a,t) \<in> valType"
shows          "envType (r (v \<mapsto> a)) (e (v \<mapsto> t))"
proof (rule envTypeI)
  fix x t1 assume A1: "(e (v\<mapsto>t)) x = Some t1"
  show "\<exists>a1. (r (v \<mapsto> a)) x = Some a1 \<and> (a1,t1) \<in> valType"
  proof cases
    assume A2: "x = v"
    hence F1: "(r (v \<mapsto> a)) x = Some a" by simp
    from A1 and A2 have "t = t1" by simp
    with F1 and valOK show ?thesis by fast
  next 
    assume A2: "x \<noteq> v"
    hence F1: "(r (v \<mapsto> a)) x = r x" by simp
    from A1 and A2 have F2: "(e (v\<mapsto>t)) x = e x" by simp
    with A1 have F3: "e x = Some t1" by simp
    with envOK obtain a1 where "r x = Some a1 \<and> (a1,t1) \<in> valType" 
                                                         using getVar by fast
    with F1 show ?thesis by simp
  qed
qed
    

(* Consing instructions are OK *)
lemma Cons_steps:
assumes instrOK: "(e,Cons v0 v1 v,e1) \<in> checkInstr pt"
    and nextOK:  "(e1,i) \<in> checkBlock pt"
    and envOK:   "envType r e"
shows            "steps pt p r (Cons v0 v1 v \<guillemotright> i)"
proof -
  from instrOK
    obtain t0 t1 t where tV0:    "e v0 = Some t0"
                     and tV1:    "e v1 = Some t1"
                     and tV:     "lub (TList t0) t1 = TList t"
                     and e1_def: "e1 = e (v \<mapsto> TCons t)" 
      by (rule checkInstr_Cons,simp)

  from envOK and tV0 
    obtain a0 where A0:  "r v0 = Some a0" 
                and tA0: "(a0,t0) \<in> valType" using getVar by fast
  from envOK and tV1 
    obtain a1 where A1:  "r v1 = Some a1" 
                and tA1: "(a1,t1) \<in> valType" using getVar by fast
  let ?r1 = "r(v \<mapsto> Node a0 a1)"

  from A0 and A1 
    have Step: "((r, Cons v0 v1 v \<guillemotright> i),(?r1,i)) \<in> step p" by (rule step.Cons)
    have resType: "(Node a0 a1,TCons t) \<in> valType"
    proof
      from tV and lub_sub_left [of "TList t0" t1] 
        have "(TList t0, TList t) \<in> sub" by simp
        hence "(t0,t) \<in> sub" by fast
        with tA0 show "(a0,t) \<in> valType" using cast by fast

     from tV and lub_sub_right [of t1 "TList t0"]
       have "(t1,TList t) \<in> sub" by simp
       with tA1 show "(a1, TList t) \<in> valType" using cast by fast
   qed

   from envOK resType and e1_def have "envType ?r1 e1" using updEnv by simp
   with nextOK and Step show ?thesis by auto
qed


(* Fetching instructions are OK *)
lemma Fetch_steps:
assumes instrOK: "(e,FetchField v0 f v,e1) \<in> checkInstr pt"
    and nextOK:  "(e1,i) \<in> checkBlock pt"
    and envOK:   "envType r e"             
shows "steps pt p r (FetchField v0 f v \<guillemotright> i)"
proof -
  from instrOK 
    obtain t where tV0:    "e v0 = Some (TCons t)"
               and e1_def: "e1 = e (v \<mapsto> if f = Fst then t else TList t )" 
    by (rule checkInstr_FetchField,simp)
  from envOK and tV0
    obtain a0 a1 where A:   "r v0 = Some (Node a0 a1)"
                   and tA0: "(a0,t) \<in> valType"
                   and tA1: "(a1,TList t) \<in> valType"
                                  using getVar by fast
  let ?r1 = "r (v \<mapsto> if f = Fst then a0 else a1)"
  from A have Step: "((r,FetchField v0 f v \<guillemotright> i),(?r1,i)) \<in> step p"
                                            by (rule step.Fetch)
  from envOK tA0 tA1 and e1_def have "envType ?r1 e1" using updEnv by simp
  with nextOK and Step show ?thesis by auto
qed


(* Branching instructions for Cons are OK *)
lemma Branch_Node_steps:
assumes nextOK: "(e,i) \<in> checkBlock pt" 
    and envOK:  "envType r e"
    and isNode: "r v = Some (Node a0 a1)" 
shows "steps pt p r (BranchIfNil v l \<guillemotright> i)"
proof -
  have Step: "((r,BranchIfNil v l \<guillemotright> i),(r,i)) \<in> step p" by (rule step.BranchNot)
  with prems show ?thesis by (simp, fast)
qed


(* Branching instructions for Nil are OK *)
lemma Branch_Null_steps:
assumes progOK: "checkProg pt p"
    and envOK:  "envType r e"
    and isNull: "r v = Some Null"
    and labOK:  "pt l = Some e1"
    and subEnv: "subEnv e e1" 
shows "steps pt p r (BranchIfNil v l \<guillemotright> i)"
proof -
 from progOK labOK 
    obtain k where tgtCode: "p l = Some k" 
               and tgtOK:   "(e1,k) \<in> checkBlock pt" using getCode by fast
  from isNull tgtCode
    have Step: "((r,BranchIfNil v l \<guillemotright> i),(r,k)) \<in> step p" 
     by (rule step.BranchYes)
  from envOK subEnv have "envType r e1" using castEnv by fast
  with Step tgtOK show ?thesis by (simp,fast)
qed


(* Branching instructiosn are OK *)
lemma Branch_steps:
assumes progOK:  "checkProg pt p"
    and instrOK: "(e,BranchIfNil v l,e1) \<in> checkInstr pt"
    and nextOK:  "(e1,i) \<in> checkBlock pt" 
    and envOK:   "envType r e"
shows "steps pt p r (BranchIfNil v l \<guillemotright> i)"
using instrOK proof (rule checkInstr_BranchIfNil)
  fix t assume "e v = Some (TCons t)" and "e1 = e"
  with envOK obtain a0 a1 where "r v = Some (Node a0 a1)" using getVar by fast
  with prems show ?thesis using Branch_Node_steps by fast
next
  fix e2 assume "e v = Some TNil" "pt l = Some e2" "subEnv e e2" 
  with envOK have "r v = Some Null" using getVar by fast
  with prems show ?thesis using Branch_Null_steps by fast
next
  fix e2 t assume varOK:  "e v = Some (TList t)"
              and labOK:  "pt l = Some e2"
              and subEnv: "subEnv (e(v \<mapsto> TNil)) e2"
              and e1_def: "e1 = e(v \<mapsto> TCons t)" 
  from envOK varOK   
    obtain a where A:  "r v = Some a"
               and tA: "(a,TList t) \<in> valType"  using getVar by fast
  show ?thesis using tA
  proof (rule Val_TList)
    fix x xs assume A_def:"a = Node x xs"
                and tX:   "(x,t) \<in> valType"
                and tXS:  "(xs,TList t) \<in> valType"
    hence A_type: "(a,TCons t) \<in> valType" by fast
    have envOK: "envType r e1"
    proof -
      from envOK A_type have"envType (r(v\<mapsto>a)) (e (v \<mapsto> TCons t))" 
        using updEnv by simp
      moreover from A have "r(v\<mapsto>a) = r" using map_upd_triv by fast
      ultimately show ?thesis using e1_def by simp
    qed

    from A A_def have "r v = Some (Node x xs)" by simp
    with nextOK envOK show ?thesis by (rule Branch_Node_steps) 
  next
    assume Null: "a = Null" 
    with A have isNull: "r v = Some Null" by simp
    have envOK: "envType r (e (v \<mapsto> TNil))"
    proof -
      from envOK have "envType (r (v \<mapsto> Null)) (e (v \<mapsto> TNil))"
        using updEnv by fast
      moreover from isNull have "r (v \<mapsto> Null) = r" by (rule map_upd_triv)
      ultimately show ?thesis by simp
    qed
    from progOK envOK isNull labOK subEnv 
     show ?thesis by (rule Branch_Null_steps)
  qed    
qed


(* Sequencing instructions are OK *)
lemma Seq_steps:
assumes instrOK: "(e1,i1\<guillemotright>i2,e3) \<in> checkInstr pt"
    and nextOK:  "(e3,i3) \<in> checkBlock pt"
    and envOK:   "envType r e1"
shows   "steps pt p r ((i1 \<guillemotright> i2) \<guillemotright> i3)"
proof -
  from instrOK obtain e2 where step1: "(e1,i1,e2) \<in> checkInstr pt"
                           and step2: "(e2,i2,e3) \<in> checkInstr pt" 
               by (rule checkInstr_Seq,simp)
  from step2 nextOK have "(e2, i2\<guillemotright>i3) \<in> checkBlock pt" by fast
  with step1 have "(e1,i1\<guillemotright>(i2\<guillemotright>i3)) \<in> checkBlock pt" by fast
  with envOK have "(r,i1\<guillemotright>i2\<guillemotright>i3) \<in> TypedState pt" by (simp,fast)
  moreover have "( (r,(i1\<guillemotright>i2)\<guillemotright>i3), (r,i1\<guillemotright>i2\<guillemotright>i3)) \<in> step p" by (rule step.Seq)
  ultimately show ?thesis by (simp,fast)
qed



(* In well typed programs we can either step, or we have halted. *)
lemma step_or_halt:
assumes progOK:  "checkProg pt p"
    and blockOK: "(e,i) \<in> checkBlock pt"
    and envOK:   "envType r e"
shows "steps pt p r i \<or> i = Halt"
using blockOK proof (rule checkBlock.cases)
  fix e1 assume "(e,i) = (e1,Halt)" hence "i = Halt" by simp thus ?thesis ..
next
  fix e1 e2 l assume "(e,i) = (e1,Jump l)" 
                 and "pt l = Some e2" 
                 and "subEnv e1 e2"
  with progOK envOK show ?thesis using Jump_steps by fast
next
  fix e1 e2 i1 i2 assume shape: "(e,i) = (e1,i1 \<guillemotright> i2)"
                     and instrOK: "(e1,i1,e2) \<in> checkInstr pt"
                     and nextOK:  "(e2,i2) \<in> checkBlock pt"
  show ?thesis 
  proof (cases i1)
  case BranchIfNil with prems show ?thesis using Branch_steps by fast next
  case FetchField with prems show ?thesis using Fetch_steps by fast next
  case Cons with prems show ?thesis using Cons_steps by fast next
  case Seq with prems show ?thesis using Seq_steps by simp next
  case Halt with instrOK show ?thesis 
        apply simp by (rule checkInstr_Halt,simp) next
  case Jump with instrOK show ?thesis
        apply simp by (rule checkInstr_Jump,simp)
 qed
qed


(* If a program is well-typed, then it will run. *)
theorem soundness:
assumes progOK: "checkProg pt p"
shows "runs p"
proof -
  from progOK have "pt 0 = Some initTEnv" using progOK_entry by fast
  then obtain entry where entry_def: "p 0 = Some entry" 
                      and blockOK:   "(initTEnv,entry) \<in> checkBlock pt"
       using progOK getCode by fast
  have envOK: "envType [0\<mapsto>Null] initTEnv" by (simp add: envType_def, fast)
  have "([0\<mapsto>Null], entry) \<in> goodState p" 
  proof (rule goodState.coinduct)
    from envOK blockOK show "([0\<mapsto>Null],entry) \<in> TypedState pt" by (simp,fast)

    fix z assume "z \<in> TypedState pt"
    then obtain r i e where "z = (r,i)"
                        and "(e,i) \<in> checkBlock pt"
                        and "envType r e" by (simp,fast)
      with prems have "steps pt p r i \<or> i = Halt" using step_or_halt by fast
      thus "(\<exists>s1 s2. z = s1 \<and> (s1, s2) \<in> step p 
                            \<and> s2 \<in> TypedState pt \<union> goodState p) 
          \<or> (\<exists>r. z = (r, Halt))" using prems by simp
  qed
  with entry_def show "runs p" by (simp add: runs_def)
qed

end
