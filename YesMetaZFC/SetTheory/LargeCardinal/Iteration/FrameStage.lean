import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 共尾有限框架中的首次出现阶段

阶段集合由原坐标公式分离，取内部最小阶段。零轮之外的首次出现必有真实前一阶段；
这只使用模型内部的ω良序，不假定该ω在外部标准或良基。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem It_frames_d.first_l (hZF : M.Models ZF) {n} {idx : Fin 14 → Fin (n+1)}
    {ω c D f e s₀ y : M.Domain} (h : It_frames_d hZF idx ω c D f)
    (v₀ : Fin (n+1) → M.Domain) (empty : ∀ x, ¬ M.mem x e)
    (first : Rd_entry_d e s₀ f) (code₀ : Rt_tuple_d v₀ s₀) (hy : M.mem y ω)
    (outside : ¬ M.mem y (v₀ (idx 6))) :
    ∃ i j s t, ∃ v w : Fin (n+1) → M.Domain, M.SuccessorOf j i ∧
      Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ Rd_entry_d j t f ∧ Rt_tuple_d w t ∧
      ¬ M.mem y (v (idx 6)) ∧ M.mem y (w (idx 6)) := by
  classical
  have hw := (h.read_l hZF v₀ first code₀).tree.omega
  let ρ : Env M 2 := ⟨fun i => [f,y].get i,fun _ => y⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∃ s m,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,s,⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜(rt_coord_m (idx 6))⌝ₚ(s,m) ∧ ⌜(.bound 2 : Term 3)⌝ₛ ∈ m⟫ }
  have sat k : φ.denote ρ k ↔ ∃ s m, Rd_entry_d k s f ∧ Rt_coord_d (idx 6) s m ∧ M.mem y m := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]; rfl
  obtain ⟨S,ss⟩ := ZF.separation_exists_d hZF φ ρ ω
  have stages k : M.mem k S ↔ ∃ s m, Rd_entry_d k s f ∧ Rt_coord_d (idx 6) s m ∧ M.mem y m :=
    (ss k).trans ((and_congr_right fun _ => sat k).trans ⟨And.right,fun ⟨s,m,hs,rest⟩ =>
      ⟨(h.function.bound_l hs).1,s,m,hs,rest⟩⟩)
  obtain ⟨s₁,_,h₁⟩ := h.function.2.1 y hy
  obtain ⟨v₁,p₁,frame⟩ := h.rows y s₁ h₁
  obtain ⟨j,hj,least⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF)
    ⟨y,(stages y).mpr ⟨s₁,v₁ (idx 6),h₁,⟨v₁,p₁,rfl⟩,frame.span⟩⟩
  obtain ⟨t,m,ht,coord,hym⟩ := (stages j).mp hj
  obtain ⟨w,pt,_⟩ := h.rows j t ht
  have hyw : M.mem y (w (idx 6)) := (coord.read_l w pt).symm ▸ hym
  have nonempty : ∃ x, M.mem x j := by
    apply Classical.byContradiction
    intro no
    have eq := hZF.1.eq_of_same_members j e (fun x => iff_of_false (fun hx => no ⟨x,hx⟩) (empty x))
    subst j
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 e t s₀ ht first
    subst t
    exact outside (congrFun (rt_tuple_inj_l pt code₀) (idx 6) ▸ hyw)
  obtain ⟨i,hi,succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF (h.function.bound_l ht).1 nonempty
  obtain ⟨s,_,hs⟩ := h.function.2.1 i hi
  obtain ⟨v,ps,_⟩ := h.rows i s hs
  exact ⟨i,j,s,t,v,w,succ,hs,ps,ht,pt,fun hyv =>
    least i ((stages i).mpr ⟨s,v (idx 6),hs,⟨v,ps,rfl⟩,hyv⟩) succ.predecessor_mem,hyw⟩

end YesMetaZFC.SetTheory.LargeCardinal
