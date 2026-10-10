import YesMetaZFC.Model.Forcing.Proper.Hereditary.Atomic
import YesMetaZFC.Model.Forcing.Proper.Elementary.Countable
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 初等模型内的原子成员判定集

判定“当前条件已有带权成员见证，或其后永远没有见证”。判定集是 B 的真实
子集，因而属于 H(χ)；原子绝对性使内部初等性将同一个精确判定集取到 N 中。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def At_dec_d (M : SetTheory.Structure.{u}) (B R z s t D : M.Domain) : Prop :=
  M.MemberSubset D B ∧ ∀ p, M.mem p B → (M.mem p D ↔ p ≠ z ∧
    (Wit_d M false B R z p s t ∨ Neg_d M B R z (fun q => Wit_d M false B R z q s t) p))

def at_dec_m {n} (B R z s t D : Term n) : Formula 1 n :=
  .conj (Formula.subset D B) (Formula.forallMem B (.iff (.mem .newest D.weaken)
    (.conj (.neg (Formula.extensionalEq .newest z.weaken))
      (.disj (wit_m false B.weaken R.weaken z.weaken .newest s.weaken t.weaken)
        (.forallE (.imp (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1))
          (.neg (wit_m false B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest s.weaken.weaken t.weaken.weaken))))))))
derive_free_closed at_dec_m

theorem at_dec_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z s t D : Term n) :
    Formula.satisfies ρ (at_dec_m B R z s t D) ↔
      At_dec_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (s.eval ρ) (t.eval ρ) (D.eval ρ) := by
  simp only [at_dec_m, At_dec_d, Neg_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_disj_iff,
    wit_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, below_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem at_dec_exists_l (hZF : M.Models ZF) (B R z s t : M.Domain) : ∃ D, At_dec_d M B R z s t D := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 := {
    body := .conj (.neg (Formula.extensionalEq .newest (.bound 3)))
      (.disj (wit_m false (.bound 5) (.bound 4) (.bound 3) .newest (.bound 2) (.bound 1))
        (.forallE (.imp (below_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))
          (.neg (wit_m false (.bound 6) (.bound 5) (.bound 4) .newest (.bound 3) (.bound 2)))))) }
  have hφ p : φ.denote ρ p ↔ p ≠ z ∧
      (Wit_d M false B R z p s t ∨ Neg_d M B R z (fun q => Wit_d M false B R z q s t) p) := by
    simp only [UnarySchema.denote, φ, Neg_d, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_disj_iff, wit_sat_l M hZF.1,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, below_sat_l M hZF.1]
    rfl
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨D, (fun p hp => ((hD p).mp hp).1), fun p hp => ?_⟩
  exact (hD p).trans ((and_iff_right hp).trans (hφ p))

theorem at_dec_dense_l {B R z s t D} (O : Cond_order_d M B R z) (hD : At_dec_d M B R z s t D) :
    Dense_set_d M B R z D := by
  classical
  refine ⟨fun p hp => ⟨hD.1 p hp, ((hD.2 p (hD.1 p hp)).mp hp).1⟩, fun p hp hz => ?_⟩
  by_cases h : ∃ q, Below_d M B R z q p ∧ Wit_d M false B R z q s t
  · obtain ⟨q, hq, hw⟩ := h
    exact ⟨q, hq, (hD.2 q hq.1).mpr ⟨hq.2.1, Or.inl hw⟩⟩
  · exact ⟨p, below_refl_l O hp hz, (hD.2 p hp).mpr ⟨hz, Or.inr (fun q hq hw => h ⟨q, hq, hw⟩)⟩⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H c T : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ) (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
  (hM : Smdl_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c H T)
  (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
local notation "L" => smdl_structure_l I (R := T) (And.left (And.right hM))
local notation "htr" => ZF.h_transitive_l I hZF hH
include hω hχ hωχ hH hT

theorem smem_at_dec_l (B R z s t D : (L).Domain) (hs : Name_d M B.val s.val) (ht : Name_d M B.val t.val) :
    At_dec_d L B R z s t D ↔ At_dec_d M B.val R.val z.val s.val t.val D.val := by
  have hw p : Wit_d L false B R z p s t ↔ Wit_d M false B.val R.val z.val p.val s.val t.val :=
    smem_wit_l hZFC hω hχ hωχ hH hM hT B R z p s t hs ht
  have hn p : Neg_d L B R z (fun q => Wit_d L false B R z q s t) p ↔
      Neg_d M B.val R.val z.val (fun q => Wit_d M false B.val R.val z.val q s.val t.val) p.val := by
    constructor
    · intro h q hq hqw
      let q' : (L).Domain := ⟨q, htr B.val B.property q hq.1⟩
      exact h q' ((smem_below_l I hM hT htr B R z q' p).mpr hq) ((hw q').mpr hqw)
    · exact fun h q hq hwq => h q.val ((smem_below_l I hM hT htr B R z q p).mp hq) ((hw q).mp hwq)
  have hc p : (p ≠ z ∧ (Wit_d L false B R z p s t ∨ Neg_d L B R z (fun q => Wit_d L false B R z q s t) p)) ↔
      p.val ≠ z.val ∧ (Wit_d M false B.val R.val z.val p.val s.val t.val ∨
        Neg_d M B.val R.val z.val (fun q => Wit_d M false B.val R.val z.val q s.val t.val) p.val) :=
    and_congr (not_congr ⟨congrArg Subtype.val, Subtype.ext⟩) (or_congr (hw p) (hn p))
  constructor
  · rintro ⟨hD, h⟩
    refine ⟨(smem_subset_l I hM hT htr D B).mp hD, fun p hp => ?_⟩
    let p' : (L).Domain := ⟨p, htr B.val B.property p hp⟩
    exact (smem_member_l I hM hT p' D).symm.trans
      ((h p' ((smem_member_l I hM hT p' B).mpr hp)).trans (hc p'))
  · rintro ⟨hD, h⟩
    exact ⟨(smem_subset_l I hM hT htr D B).mpr hD, fun p hp => (smem_member_l I hM hT p D).trans
      ((h p.val ((smem_member_l I hM hT p B).mp hp)).trans (hc p).symm)⟩

omit hM in
theorem selem_at_dec_l {d N S B R z s t} (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hsN : M.mem s N) (htN : M.mem t N)
    (hs : Name_d M B s) (ht : Name_d M B t) : ∃ D, M.mem D N ∧ At_dec_d M B R z s t D := by
  let A := smdl_structure_l I (R := T) hS.source.2.1
  let K := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env A 5 := ((((⟨fun _ => ⟨B, hS.subset B hB⟩, fun _ => ⟨B, hS.subset B hB⟩⟩ : Env A 1).push
    ⟨R, hS.subset R hR⟩).push ⟨z, hS.subset z hz⟩).push ⟨s, hS.subset s hsN⟩).push ⟨t, hS.subset t htN⟩
  let η : Env K 5 := ((((⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩ : Env K 1).push ⟨R, hR⟩).push
    ⟨z, hz⟩).push ⟨s, hsN⟩).push ⟨t, htN⟩
  let φ : UnarySchema 5 := { body := at_dec_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ (D : A.Domain) : φ.denote ρ D ↔ At_dec_d M B R z s t D.val :=
    (at_dec_sat_l (smem_ext_l I hS.source hT htr hZF.1) _ _ _ _ _ _ _).trans
      (smem_at_dec_l hZFC hω hχ hωχ hH hS.source hT _ _ _ _ _ D hs ht)
  obtain ⟨D, hD⟩ := at_dec_exists_l hZF B R z s t
  have hDH := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (hS.subset B hB) D hD.1
  obtain ⟨D', hD'⟩ := selem_witness_l I hZF hω hS he φ ρ η
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
    ⟨⟨D, hDH⟩, (hφ _).mpr hD⟩
  exact ⟨D'.val, D'.property, (hφ _).mp hD'⟩

end YesMetaZFC.Model.Forcing.Internal
