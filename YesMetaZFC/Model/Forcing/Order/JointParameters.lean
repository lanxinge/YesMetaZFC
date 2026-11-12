import YesMetaZFC.Model.SetTheory.Internal.Registration
import YesMetaZFC.SetTheory.Descriptive.Coding.SequenceCons

/-! # 联合树的固定参数列

将条件域与序关系接在给定参数列之前，实际构造一张原模型中的 ω 列。
参数登记因而强制每条联合枝的壳包含偏序及给定列的全部值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u
variable {M : Structure.{u}}

structure Jt_params_d (ω X Q T C : M.Domain) : Prop where
  function : Fn0_d ω X C
  conditions : ∃ i, Rd_entry_d i Q C
  order : ∃ i, Rd_entry_d i T C

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem jt_params_l {ω X Q T B : M.Domain} (hw : M.IsOmega ω) (hQ : M.mem Q X) (hT : M.mem T X)
    (fb : Fn0_d ω X B) : ∃ C, Jt_params_d ω X Q T C ∧
      ∀ i x, Rd_entry_d i x B → ∃ k, Rd_entry_d k x C := by
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨B',fb',first⟩ := cons_omega_l I hZF hw empty hT (fn0_function_l (ZF.modelsKP hZF) fb)
  obtain ⟨C,fc,second⟩ := cons_omega_l I hZF hw empty hQ fb'
  obtain ⟨one,succ,_⟩ := hw.1.2 o ho
  refine ⟨C,⟨fn0_of_function_l (ZF.modelsKP hZF) fc,⟨o,(second.2 o Q).mpr (Or.inl ⟨rfl,rfl⟩)⟩,
    ⟨one,(second.2 one T).mpr (Or.inr ⟨o,(first.2 o T).mpr (Or.inl ⟨rfl,rfl⟩),succ⟩)⟩⟩,?_⟩
  intro i x ix
  obtain ⟨j,next,hj⟩ := hw.1.2 i (fb.bound_l ix).1
  obtain ⟨k,next',_⟩ := hw.1.2 j hj
  exact ⟨k,(second.2 k x).mpr (Or.inr ⟨j,(first.2 j x).mpr (Or.inr ⟨i,ix,next⟩),next'⟩)⟩

/-- 有限指定参数和原无限参数列一同登记，随后加入偏序的两项参数。 -/
theorem jt_params_finite_l {ω X Q T B : M.Domain} (hw : M.IsOmega ω) (hQ : M.mem Q X) (hT : M.mem T X)
    (fb : Fn0_d ω X B) {n} (s : Fin n → M.Domain) (inside : ∀ i, M.mem (s i) X) :
    ∃ C, Jt_params_d ω X Q T C ∧ (∀ i, ∃ k, Rd_entry_d k (s i) C) ∧
      ∀ i x, Rd_entry_d i x B → ∃ k, Rd_entry_d k x C := by
  obtain ⟨o,empty,_⟩ := hw.1.1
  have prepend : ∀ n (s : Fin n → M.Domain), (∀ i, M.mem (s i) X) →
      ∃ C, Fn0_d ω X C ∧ (∀ i, ∃ k, Rd_entry_d k (s i) C) ∧
        ∀ i x, Rd_entry_d i x B → ∃ k, Rd_entry_d k x C := by
    intro n
    induction n with
    | zero => exact fun _ _ => ⟨B,fb,(fun i => Fin.elim0 i),fun i _ ix => ⟨i,ix⟩⟩
    | succ n ih =>
      intro s inside
      obtain ⟨C,fc,points,old⟩ := ih (fun i => s i.succ) (fun i => inside i.succ)
      obtain ⟨D,fd,cons⟩ := cons_omega_l I hZF hw empty (inside 0) (fn0_function_l (ZF.modelsKP hZF) fc)
      have next {i x} (ix : Rd_entry_d i x C) : ∃ k, Rd_entry_d k x D := by
        obtain ⟨k,succ,_⟩ := hw.1.2 i (fc.bound_l ix).1
        exact ⟨k,(cons.2 k x).mpr (Or.inr ⟨i,ix,succ⟩)⟩
      exact ⟨D,fn0_of_function_l (ZF.modelsKP hZF) fd,
        Fin.cases ⟨o,(cons.2 o (s 0)).mpr (Or.inl ⟨rfl,rfl⟩)⟩ (fun i => (points i).elim fun _ edge => next edge),
        fun i x ix => (old i x ix).elim fun _ edge => next edge⟩
  obtain ⟨D,fd,points,old⟩ := prepend n s inside
  obtain ⟨C,params,cover⟩ := jt_params_l hZF hw hQ hT fd
  exact ⟨C,params,fun i => (points i).elim fun k edge => cover k (s i) edge,
    fun i x ix => (old i x ix).elim fun k edge => cover k x edge⟩

end YesMetaZFC.Model.Forcing.Internal
