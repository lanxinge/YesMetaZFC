import YesMetaZFC.SetTheory.InnerModel.OD.Definition
import YesMetaZFC.SetTheory.CumulativeCertificate
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded

/-! # OD 的实际 Σ₂ 证书

将既有单序数解码公式限制在一个真实 V 层，层内唯一性成为 Δ₀ 条件。
有限反射证明这种表示覆盖既有 OD；反向以层高度和解码序数唯一指定对象。
累积层的全称递归证书给出最终的 ∃∃∃∃∃∀Δ₀ 正规形。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

def Od_rank_d (X q x : M.Domain) : Prop := M.IsOrdinal q ∧ M.mem q X ∧ M.mem x X ∧
  ∀ y, M.mem y X → (Lr_truth_d (od_eval_s kpair_convention_l) X q y ↔ y = x)

def od_rank_m {d} (X q x : Term d) : Formula 1 d :=
  .conj (KP.ord0_m q) (.conj (.mem q X) (.conj (.mem x X) (Formula.forallMem X
    (.iff (lr_truth_m (od_eval_s kpair_convention_l) X.weaken q.weaken .newest)
      (Formula.extensionalEq .newest x.weaken)))))
derive_free_closed od_rank_m

theorem od_rank_delta_l {d} (X q x : Term d) : (od_rank_m X q x).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (.mem _ _) (.conj (.mem _ _)
    (.forallMem _ (.iff (lr_truth_delta_l ..) (.atom _ _ _)))))

theorem od_rank_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X q x : Term d) :
    Formula.satisfies ρ (od_rank_m X q x) ↔ Od_rank_d (X.eval ρ) (q.eval ρ) (x.eval ρ) := by
  simp only [od_rank_m, Od_rank_d, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    lr_truth_sat_l, Formula.satisfies_extensionalEq_iff_eq hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem od_rank_sound_l (hZF : M.Models ZF) {a X q x : M.Domain}
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) a X) (h : Od_rank_d X q x) : Od_d x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : UnarySchema 2 := { body := .existsE (.conj
    (v_m kpair_convention_l (.bound 3) .newest) (.conj (.mem (.bound 1) .newest)
      (lr_truth_m (od_eval_s kpair_convention_l) .newest (.bound 2) (.bound 1)))) }
  let ρ : Env M 2 := ⟨Fin.cases q (fun _ => a), fun _ => a⟩
  have sat y : φ.denote ρ y ↔ ∃ Y, V_d I a Y ∧ M.mem y Y ∧ Lr_truth_d (od_eval_s kpair_convention_l) Y q y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      v_sat_l I hZF.1, Formula.satisfies_mem_iff, lr_truth_sat_l]
    rfl
  refine od_of_unique_l hZF φ ρ (Fin.cases h.1 (fun _ => v_ordinal_l I hX)) (fun y => (sat y).trans ?_)
  refine ⟨fun ⟨Y, hy, hym, ht⟩ => ?_, fun he => he.symm ▸ ⟨X, hX, h.2.2.1, (h.2.2.2 x h.2.2.1).mpr rfl⟩⟩
  have eq := ZF.v_unique_l I hZF hy hX; subst Y
  exact (h.2.2.2 y hym).mp ht

theorem od_rank_complete_l (hZF : M.Models ZF) {x : M.Domain} (h : Od_d x) :
    ∃ a X q, V_d (kp_pair_l (ZF.modelsKP hZF)) a X ∧ Od_rank_d X q x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨q, hq⟩ := (od_code_range_l I hZF).mp h
  obtain ⟨A, hA⟩ := KP.exists_pair (ZF.modelsKP hZF) q x
  let φ := od_eval_s kpair_convention_l
  obtain ⟨a, X, hX, hAX, hr⟩ := ZF.lr_reflect_l I hZF φ.body φ.freeClosed A
  have ht := ZF.v_transitive_l I hZF hX
  have hqX := ht A hAX q ((hA q).mpr (Or.inl rfl))
  have hxX := ht A hAX x ((hA x).mpr (Or.inr rfl))
  obtain ⟨c, R, hM, hR⟩ := smdl_membership_l I hZF ⟨x, hxX⟩
  refine ⟨a, X, q, hX, od_eval_ordinal_l I hZF hq, hqX, hxX, fun y hy => ?_⟩
  exact (lr_truth_reflect_l I hM hR ht φ hr hqX hy).trans
    ((od_eval_sat_l I hZF.1 _ _ _).trans
      ⟨fun hy => od_eval_unique_l I hZF hy hq, fun he => he.symm ▸ hq⟩)

def od_sigma_m {d} (x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.forallE
    (.conj (vc_matrix_m (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest)
      (od_rank_m (.bound 3) (.bound 4) x.weaken.weaken.weaken.weaken.weaken.weaken)))))))
derive_free_closed od_sigma_m

theorem od_sigma_complexity_l {d} (x : Term d) : (od_sigma_m x).IsSigma2 :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.lift (.forallE (.lift
    (.base (.conj (vc_matrix_delta_l ..) (od_rank_delta_l ..))))))))))

/-- 实际 ∃∃∃∃∃∀Δ₀ 公式与既有无参数 OD 谓词等价。 -/
theorem od_sigma_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (x : Term d) :
    Formula.satisfies ρ (od_sigma_m x) ↔ Od_d (x.eval ρ) := by
  simp only [od_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_conj_iff, vc_matrix_sat_l (ZF.modelsKP hZF), od_rank_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨a, q, X, B, F, h⟩
    exact od_rank_sound_l hZF (vc_sound_l (ZF.modelsKP hZF) (fun t => (h t).1)) (h (x.eval ρ)).2
  · intro h
    obtain ⟨a, X, q, hX, hr⟩ := od_rank_complete_l hZF h
    obtain ⟨B, F, hc⟩ := vc_complete_l (ZF.modelsKP hZF) hX
    exact ⟨a, q, X, B, F, fun t => ⟨hc t, hr⟩⟩

end YesMetaZFC.SetTheory.InnerModel
