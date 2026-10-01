import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Coherence
import YesMetaZFC.Model.Forcing.Internal.Check.Order
import YesMetaZFC.SetTheory.RelationChain

/-! # 全部早期名称在同一旧偏序中的加强关系

将实际状态 (p,τ) 放入旧偏序与其规范名称的二步序。商成员给出真实条件性，
每次转移给出该序上的加强；可定义传递关系的内部 ω 归纳随后处理任意早期状态。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_pr_thread_resolve_l (I : kpair_convention_l.Interpretation M) {F G b D N A i x α B R}
    (ha : ∀ i α β, Entry_d M i α A → Entry_d M i β A → α = β)
    (hf : ∀ i B C, Entry_d M i B F → Entry_d M i C F → B = C)
    (hg : ∀ i R T, Entry_d M i R G → Entry_d M i T G → R = T)
    (hx : Row_pr_thread_d I F G b D N A i x) (hi : Entry_d M i α A)
    (hB : Entry_d M α B F) (hR : Entry_d M α R G) : Row_pr_state_d I α B R b D N x := by
  obtain ⟨β, C, T, hj, hC, hT, hx⟩ := hx
  have he := ha i β α hj hi
  subst β
  exact hf α C B hC hB ▸ hg α T R hT hR ▸ hx

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_order_l {ω δ F G b β D V N A Z E X Q C T}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hA : M.IsSetFunctionFromTo I A ω Z)
    (hi : ∀ i α, Entry_d M i α A → M.MemberSubset α β)
    (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i y, Entry_d M i y Q → Row_pr_thread_d I F G b D N A i y)
    (hs : ∀ i j y z, M.SuccessorOf j i → Entry_d M i y Q → Entry_d M j z Q →
      Row_pr_advance_d I F G b D V N A E i y z)
    (hC : Check_d M b D C) (hT : Check_d M b V T) :
    (∀ i x, Entry_d M i x Q → Step_named_d M D V D b C x) ∧
      ∀ i j x y, M.mem i j → Entry_d M i x Q → Entry_d M j y Q → Step_le_d M D V D T y x := by
  have s := h.stages β D V hD hV
  have cn := check_name_l M (check_range_l M hZF) s.base hC
  have tn := check_name_l M (check_range_l M hZF) s.base hT
  have hp := check_preord_force_l s.order hZF s.base hC hT ⟨s.order.refl, s.order.trans⟩
    (below_refl_l s.order s.base (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ s.base)))
  have named i x (hx : Entry_d M i x Q) : Step_named_d M D V D b C x := by
    obtain ⟨α, B, R, hα, hB, hR, p, τ, K, hx, hm, hτ, hK, hτK⟩ := hv i x hx
    have t := h.stages α B R hB hR
    have k := h.links α β B R D V hB hR hD hV (hi i α hα)
    have hcn := check_name_l M (check_range_l M hZF) t.base hC
    exact ⟨p, τ, hx, row_name_l k hτ,
      ⟨k.mem p hm.1, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ k.mem p hm.1)),
        (k.order p b hm.1 t.base).mpr (t.top p hm.1)⟩,
      (row_mem_force_l hZF t.order s.order k hm.1 hτ hcn).mp
        (row_quot_subset_l hZF t.order t.base hK (fun _ hr _ => hr) hC (t.top p hm.1) hτK)⟩
  have step i j x y (hj : M.SuccessorOf j i) (hx : Entry_d M i x Q) (hy : Entry_d M j y Q) :
      Step_le_d M D V D T y x := by
    obtain ⟨j', α, B, R, γ, B', R', U, hj', hiα, hjγ, hB, hR, hB', hR', _, hm⟩ := hs i j x y hj hx hy
    have he := hZF.1.eq_of_same_members j' j (fun t => (hj' t).trans (hj t).symm)
    subst j'
    obtain ⟨p, τ, q, σ, K, ν, η, hxp, hyq, hpq, hσ, _, hν, _, _, _, hστ, _⟩ := hm
    obtain ⟨p', τ', _, hx', hpm, hτ, _⟩ := row_pr_thread_resolve_l I hA.1.2 h.conditions.2.1.2 h.relations.2.1.2
      (hv i x hx) hiα hB hR
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hxp hx'
    obtain ⟨q', σ', _, hy', hqm, _⟩ := row_pr_thread_resolve_l I hA.1.2 h.conditions.2.1.2 h.relations.2.1.2
      (hv j y hy) hjγ hB' hR'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hyq hy'
    have t := h.stages α B R hB hR
    have k := h.links α β B R D V hB hR hD hV (hi i α hiα)
    have l := h.links γ β B' R' D V hB' hR' hD hV (hi j γ hjγ)
    have hq := l.mem q hqm.1
    have hqp : Below_d M D V D q p := ⟨hq,
      (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hq)), k.below q p hq hpq⟩
    have heν := check_unique_l M hZF.1 (check_ind_l M hZF) b V ν T hν hT
    subst ν
    have hn := check_name_l M (check_range_l M hZF) t.base hT
    exact (step_le_iff_l hyq hxp).mpr ⟨hqp,
      (rel_force_regular_l s.order hZF tn (row_name_l k hσ) (row_name_l k hτ)).1 p q (k.mem p hpm.1) hqp
        ((row_rel_force_l hZF t.order s.order k hpm.1 hn hσ hτ).mp hστ)⟩
  let ρ : Env M 5 := ⟨Fin.cases D (Fin.cases V (Fin.cases b (Fin.cases C (fun _ => T)))), fun _ => b⟩
  let φ : BinarySchema 5 := {
    body := .conj (step_named_m (.bound 2) (.bound 3) (.bound 2) (.bound 4) (.bound 5) (.bound 1))
      (.conj (step_named_m (.bound 2) (.bound 3) (.bound 2) (.bound 4) (.bound 5) .newest)
        (step_le_m (.bound 2) (.bound 3) (.bound 2) (.bound 6) .newest (.bound 1))) }
  have hφ x y : φ.denote ρ x y ↔ Step_named_d M D V D b C x ∧ Step_named_d M D V D b C y ∧ Step_le_d M D V D T y x := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, step_named_sat_l M hZF.1, step_le_sat_l M hZF.1]
    rfl
  have chain := ZF.rel_chain_l I hZF φ ρ hω hQ (by
    intro x y z _ _ _ hxy hyz
    obtain ⟨hx, hy, hxy⟩ := (hφ x y).mp hxy
    obtain ⟨_, hz, hyz⟩ := (hφ y z).mp hyz
    exact (hφ x z).mpr ⟨hx, hz, step_named_trans_l s.order hZF cn tn s.base hp hz hy hx hyz hxy⟩)
    (fun i j x y hj hx hy => (hφ x y).mpr ⟨named i x hx, named j y hy, step i j x y hj hx hy⟩)
  exact ⟨named, fun i j x y hij hx hy => ((hφ x y).mp (chain i j x y hij hx hy)).2.2⟩

end YesMetaZFC.Model.Forcing.Internal
