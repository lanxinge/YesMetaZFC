import YesMetaZFC.Model.Forcing.Proper.Generic.Hull
import YesMetaZFC.Model.Forcing.Proper.Elementary.Membership
import YesMetaZFC.Model.Forcing.Internal.Maximum.WitnessPool
import YesMetaZFC.Model.Forcing.Internal.Forcing.Rules
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 主条件下的实际存在见证提升

先在地模型中构造加权见证池 A 及判定其非空纤维的稠密集 D。若内部初等 N
含这两个实际集合，接受 N 主条件的泛型就从 N 中取得见证名称。这里仅用 ZF，
不要求 N 传递，不调用选择公理，也不假定已有 N[G] 的初等性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 见证池及判定集的具体方程，由下方的原 ZF 构造直接提供实例。 -/
structure Ng_witness_d {n} (φ : UnarySchema n) (ρ : Env M n) (A D : M.Domain) : Prop where
  name : Name_d M B A
  sound : ∀ s p, Entry_d M s p A → Forces_d M B R z φ.body (ρ.push s) p
  cover : ∀ p, M.mem p B → ∀ s, Name_d M B s → Forces_d M B R z φ.body (ρ.push s) p →
    ∃ t, Entry_d M t p A
  decide : ∀ p, M.mem p D ↔ M.mem p B ∧ p ≠ z ∧
    ((∃ s, Entry_d M s p A) ∨ Neg_d M B R z (fun q => ∃ s, Entry_d M s q A) p)

/-- 对任意原存在公式及名称参数实际构造两件提升数据；构造时尚未指定泛型或 N。 -/
theorem ng_witness_data_l (hZF : M.Models ZF) {n} (φ : UnarySchema n) (ρ : Env M n) :
    ∃ A D, Ng_witness_d (B := B) (R := R) (z := z) φ ρ A D := by
  obtain ⟨A, hA, hs, hc⟩ := witness_pool_l hZF φ ρ
  let η : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let ψ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 1) (.bound 2)) }
  have hψ p : ψ.denote η p ↔ ∃ s, Entry_d M s p A := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨k, χ, δ, hχ⟩ := defined_decide_l M hZF.1 ⟨1, ψ, η, hψ⟩ B R z
  let θ : UnarySchema (k+1) := {
    body := .conj (.neg (Formula.extensionalEq .newest (.bound 1)))
      (pred_m χ (fun i => .bound ⟨i.val+2, by omega⟩) .newest) }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF θ (δ.push z) B
  refine ⟨A, D, hA, hs, hc, fun p => (hD p).trans (and_congr_right fun _ => ?_)⟩
  simp only [θ, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, pred_sat_l M]
  exact and_congr Iff.rfl (hχ p)

theorem Ng_witness_d.dense_l (O : Cond_order_d M B R z) {n φ ρ A D}
    (h : @Ng_witness_d M B R z n φ ρ A D) : Dense_set_d M B R z D := by
  classical
  refine ⟨fun p hp => ⟨((h.decide p).mp hp).1, ((h.decide p).mp hp).2.1⟩, fun p hp hz => ?_⟩
  by_cases he : ∃ q, Below_d M B R z q p ∧ ∃ s, Entry_d M s q A
  · obtain ⟨q, hq, hs⟩ := he
    exact ⟨q, hq, (h.decide q).mpr ⟨hq.1, hq.2.1, Or.inl hs⟩⟩
  · exact ⟨p, below_refl_l O hp hz, (h.decide p).mpr
      ⟨hp, hz, Or.inr (fun q hq hs => he ⟨q, hq, hs⟩)⟩⟩

/-- 泛型接受主条件时，实际见证名称来自 N；正文仍在整个泛型扩张中成立。 -/
theorem Ng_witness_d.generic_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {ω c d X T N S A D q}
    (hω : M.IsOmega ω) (hS : Ssub_d I c d X T N S) (hN : Selem_d I ω c d)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
    (hX : M.TransitiveSet X) (hA : M.mem A N) (hD : M.mem D N) (hm : Mstr_d M B R z N q)
    {n φ ρ} (h : @Ng_witness_d M B R z n φ ρ A D) {U : M.Domain → Prop}
    (hU : Generic_d M B R z U) (hq : U q)
    (η : Env (extension_l M hZF B R z U) n) (hρ : Env_val_d hZF ρ η)
    (he : ∃ x, φ.denote η x) : ∃ y, Ng_mem_d M B R z U N y ∧ φ.denote η y := by
  obtain ⟨p, hpN, hpD, hpU⟩ := mstr_generic_l hZF hU hq hm hD (h.dense_l O)
  have active : ∃ s, Entry_d M s p A := by
    rcases ((h.decide p).mp hpD).2.2 with hs | hn
    · exact hs
    · obtain ⟨x, hx⟩ := he
      obtain ⟨t, ht, htx⟩ := value_name_l (M := M) (B := B) (R := R) (z := z) (U := U) x
      have hρt := env_val_push_l hZF hρ htx
      obtain ⟨r, hr, hφ⟩ := (forcing_truth_l O hZF hU φ.body φ.freeClosed
        (ρ.push t) (η.push x) hρt).mpr hx
      obtain ⟨v, hv, hvp, hvr⟩ := hU.directed p r hpU hr
      have hv' := hU.proper v hv
      have hφv := (forces_regular_l O hZF φ.body (ρ.push t) (fun t => qval_name_l (hρt t))).1
        r v (hU.proper r hr).1 ⟨hv'.1, hv'.2, hvr⟩ hφ
      exact (hn v ⟨hv'.1, hv'.2, hvp⟩ (h.cover v hv'.1 t ht hφv)).elim
  obtain ⟨s, hsN, hsp⟩ := selem_entry_witness_l I hT hX hZF hω hS hN hA hpN active
  obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) (name_entry_l M h.name hsp).1
  exact ⟨y, ⟨s, hsN, hy⟩, (forcing_truth_l O hZF hU φ.body φ.freeClosed
    (ρ.push s) (η.push y) (env_val_push_l hZF hρ hy)).mp ⟨p, hpU, h.sound s p hsp⟩⟩

end YesMetaZFC.Model.Forcing.Internal
