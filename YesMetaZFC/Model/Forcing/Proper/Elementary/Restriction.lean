import YesMetaZFC.Model.Forcing.Proper.Elementary.FirstPreimage
import YesMetaZFC.Model.Forcing.Internal.Reflection.Transitive

/-! # 限制图的传递绝对性与内部初等闭包

限制图及原图的每个有序对都在传递环境中，故条目的两个坐标也在其中。
原 ZF 构造的限制是原图的子集；H(χ) 对子集封闭，初等性将唯一限制取回 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

private theorem restriction_raw_sat_l (hE : Extensional M) {n} (ρ : Env M n) (a r α : Term n) :
    Formula.satisfies ρ (Formula.isRestriction kpair_convention_l a r α) ↔
      (∀ v, M.mem v (a.eval ρ) → ∃ i s, KPair_d M v i s) ∧
        ∀ i s, Entry_d M i s (a.eval ρ) ↔ M.mem i (α.eval ρ) ∧ Entry_d M i s (r.eval ρ) := by
  simp only [Formula.isRestriction, Formula.isRelation, Formula.orderedPairMem, kpair_convention_l, Entry_d,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem smem_restriction_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c H T}
    (hM : Smdl_d I c H T) (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hH : M.TransitiveSet H) (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {n}
    (ρ : Env (smdl_structure_l I (R := T) hM.2.1) n) (a r α : Term n) :
    Formula.satisfies ρ (Formula.isRestriction kpair_convention_l a r α) ↔
      M.IsRestrictionOf (kpair_interpretation_l M hE hP) (a.eval ρ).val (r.eval ρ).val (α.eval ρ).val := by
  let L := smdl_structure_l I (R := T) hM.2.1
  let A := a.eval ρ
  let R := r.eval ρ
  let S := α.eval ρ
  rw [restriction_raw_sat_l (smem_ext_l I hM hT hH hE)]
  change ((∀ v, L.mem v A → ∃ i s, KPair_d L v i s) ∧
    ∀ i s, Entry_d L i s A ↔ L.mem i S ∧ Entry_d L i s R) ↔
    (∀ v, M.mem v A.val → ∃ i s, KPair_d M v i s) ∧
    ∀ i s, Entry_d M i s A.val ↔ M.mem i S.val ∧ Entry_d M i s R.val
  apply and_congr
  · constructor
    · intro hg v hv
      let v' : L.Domain := ⟨v, hH A.val A.property v hv⟩
      obtain ⟨i, s, his⟩ := hg v' ((smem_member_l I hM hT v' A).mpr hv)
      exact ⟨i.val, s.val, (smem_kpair_l I hM hT hH v' i s).mp his⟩
    · intro hg v hv
      obtain ⟨i, s, his⟩ := hg v.val ((smem_member_l I hM hT v A).mp hv)
      have ht := trans_kpair_l hH v.property his
      exact ⟨⟨i, ht.1⟩, ⟨s, ht.2⟩, (smem_kpair_l I hM hT hH v _ _).mpr his⟩
  · constructor
    · intro hh i s
      constructor
      · intro his
        have ht := trans_entry_l hH A.property his
        let i' : L.Domain := ⟨i, ht.1⟩
        let s' : L.Domain := ⟨s, ht.2⟩
        have h := (hh i' s').mp ((smem_entry_l I hM hT hH i' s' A).mpr his)
        exact ⟨(smem_member_l I hM hT i' S).mp h.1, (smem_entry_l I hM hT hH i' s' R).mp h.2⟩
      · rintro ⟨hi, his⟩
        have ht := trans_entry_l hH R.property his
        let i' : L.Domain := ⟨i, ht.1⟩
        let s' : L.Domain := ⟨s, ht.2⟩
        exact (smem_entry_l I hM hT hH i' s' A).mp ((hh i' s').mpr
          ⟨(smem_member_l I hM hT i' S).mpr hi, (smem_entry_l I hM hT hH i' s' R).mpr his⟩)
    · intro hh i s
      exact (smem_entry_l I hM hT hH i s A).trans ((hh i.val s.val).trans
        (and_congr (smem_member_l I hM hT i S) (smem_entry_l I hM hT hH i s R)).symm)

/-- N 中两个参数所确定的实际限制图仍属于 N；只需 ZF 和 χ 为极限序数。 -/
theorem selem_restriction_l (hZF : M.Models ZF) {ω χ H c T d N S α p q}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y T ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H T N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hα : M.mem α N) (hp : M.mem p N)
    (hq : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) q p α) : M.mem q N := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let L := smdl_structure_l I (R := T) hSub.source.2.1
  let Q := smdl_structure_l I (R := S) hSub.target.2.1
  let ρ : Env L 2 := (⟨fun _ => ⟨p, hSub.subset p hp⟩, fun _ => ⟨p, hSub.subset p hp⟩⟩ : Env L 1).push ⟨α, hSub.subset α hα⟩
  let η : Env Q 2 := (⟨fun _ => ⟨p, hp⟩, fun _ => ⟨p, hp⟩⟩ : Env Q 1).push ⟨α, hα⟩
  let φ : UnarySchema 2 := { body := Formula.isRestriction kpair_convention_l .newest (.bound 2) (.bound 1) }
  have htr := ZF.h_transitive_l I hZF hH
  have hφ (a : L.Domain) : φ.denote ρ a ↔ M.IsRestrictionOf I a.val p α :=
    smem_restriction_l I hSub.source hT htr hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) _ _ _ _
  have hqp : M.MemberSubset q p := by
    intro v hv
    obtain ⟨i, s, his⟩ := hq.1 v hv
    obtain ⟨w, hw, hwp⟩ := ((hq.2 i s).mp ⟨v, his, hv⟩).2
    exact I.unique hw his ▸ hwp
  have hqH := ZF.h_subsets_l I hZF hχ hH (hSub.subset p hp) q hqp
  obtain ⟨a, ha⟩ := selem_witness_l I hZF hω hSub hElem φ ρ η (Fin.cases rfl (fun _ => rfl))
    ⟨⟨q, hqH⟩, (hφ _).mpr hq⟩
  exact (((hφ _).mp ha).eq hZF.1 hq) ▸ a.property

end YesMetaZFC.Model.Forcing.Internal
