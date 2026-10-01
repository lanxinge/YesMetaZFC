import YesMetaZFC.Model.Forcing.Proper.Elementary.Restriction
import YesMetaZFC.Model.Forcing.Iteration.Condition.Support

/-! # 内部初等模型中的条件支撑

支撑是实际图的定义域。其全部坐标落在原图的传递闭包中，故支撑仍属于 H(χ)；
内部初等性将唯一的定义域取回 N，再由可数集合闭包得到支撑包含于 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem smem_coord_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c H T}
    (hM : Smdl_d I c H T) (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hH : M.TransitiveSet H) (p D : (smdl_structure_l I (R := T) hM.2.1).Domain) :
    Coord_d (smdl_structure_l I (R := T) hM.2.1) p D ↔ Coord_d M p.val D.val := by
  let L := smdl_structure_l I (R := T) hM.2.1
  constructor
  · intro h i
    constructor
    · intro hi
      let i' : L.Domain := ⟨i, hH D.val D.property i hi⟩
      obtain ⟨s, hs⟩ := (h i').mp ((smem_member_l I hM hT i' D).mpr hi)
      exact ⟨s.val, (smem_entry_l I hM hT hH i' s p).mp hs⟩
    · rintro ⟨s, hs⟩
      have ht := trans_entry_l hH p.property hs
      let i' : L.Domain := ⟨i, ht.1⟩
      exact (smem_member_l I hM hT i' D).mp ((h i').mpr
        ⟨⟨s, ht.2⟩, (smem_entry_l I hM hT hH i' _ p).mpr hs⟩)
  · intro h i
    rw [smem_member_l I hM hT i D, h i.val]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨⟨s, (trans_entry_l hH p.property hs).2⟩, (smem_entry_l I hM hT hH i _ p).mpr hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨s.val, (smem_entry_l I hM hT hH i s p).mp hs⟩

/-- 实际坐标集属于 N；不要求原图单值、支撑可数或 χ 正则。 -/
theorem selem_coord_l (hZF : M.Models ZF) {ω χ H c T d N S p D}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y T ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H T N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hp : M.mem p N) (hD : Coord_d M p D) : M.mem D N := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let L := smdl_structure_l I (R := T) hSub.source.2.1
  let Q := smdl_structure_l I (R := S) hSub.target.2.1
  let ρ : Env L 1 := ⟨fun _ => ⟨p, hSub.subset p hp⟩, fun _ => ⟨p, hSub.subset p hp⟩⟩
  let η : Env Q 1 := ⟨fun _ => ⟨p, hp⟩, fun _ => ⟨p, hp⟩⟩
  let φ : UnarySchema 1 := { body := coord_m (.bound 1) .newest }
  have htr := ZF.h_transitive_l I hZF hH
  have hφ (a : L.Domain) : φ.denote ρ a ↔ Coord_d M p a.val :=
    (coord_sat_l L (smem_ext_l I hSub.source hT htr hZF.1) _ _ _).trans
      (smem_coord_l I hSub.source hT htr _ a)
  obtain ⟨U, μ, hU, hμ, hu⟩ := (hH p).mp (hSub.subset p hp)
  have hDH := (hH D).mpr (ZF.hmem_of_subset_l I hZF hχ hU.1 (fun i hi => by
    obtain ⟨s, hs⟩ := (hD i).mp hi
    exact (trans_entry_l hU.1 hU.2.1 hs).1) hμ hu)
  obtain ⟨a, ha⟩ := selem_witness_l I hZF hω hSub hElem φ ρ η (fun _ => rfl)
    ⟨⟨D, hDH⟩, (hφ _).mpr hD⟩
  exact coord_unique_l M hZF.1 ((hφ _).mp ha) hD ▸ a.property

/-- N 中可数支撑条件的每个非平凡坐标都属于 N，包括内部非标准指标。 -/
theorem row_supp_subset_model_l (hZFC : M.Models ZFC) {ω χ H c T d N S p}
    (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ)
    (hωχ : M.mem ω χ)
    (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
    (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y T ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c d H T N S)
    (hElem : Selem_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω c d)
    (hωN : M.mem ω N) (hp : M.mem p N)
    (hs : Row_supp_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) true ω p) :
    ∀ i s, Entry_d M i s p → M.mem i N := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨D, hD, hd⟩ := hs
  have hDN := selem_coord_l hZF hω hχ.isLimitOrdinal hH hT hSub hElem hp hD
  have hDN' := selem_countable_subset_l I hT hZFC hω hχ hωχ hH hSub hElem hωN hDN hd
  exact fun i s his => hDN' i ((hD i).mpr ⟨s, his⟩)

end YesMetaZFC.Model.Forcing.Internal
