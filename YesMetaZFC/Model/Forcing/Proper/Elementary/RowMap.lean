import YesMetaZFC.Model.Forcing.Iteration.Condition.Absoluteness
import YesMetaZFC.Model.Forcing.Iteration.Names.Representation
import YesMetaZFC.Model.Forcing.Proper.Master.Map

/-! # 同一个内部 N 中的坐标重编码图

重编码图受两个载体的乘积所界。其精确有界方程在 H(χ) 中绝对，内部初等性
给出 N 内的同一个图；由此可直接搬运主条件，而无需重新选择小模型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_map_d (M : SetTheory.Structure.{u}) (α t C D F : M.Domain) : Prop :=
  (∀ v, M.mem v F → ∃ c q, M.mem c C ∧ M.mem q D ∧ KPair_d M v c q) ∧
  ∀ c q, M.mem c C → M.mem q D → (Entry_d M c q F ↔ Row_code_d M α t c q)

def row_map_m {n} (α t C D F : Term n) : Formula 1 n :=
  .conj (Formula.forallMem F (.existsE (.existsE
    (.conj (.mem (.bound 1) C.weaken.weaken.weaken) (.conj (.mem .newest D.weaken.weaken.weaken)
      (kpair_m (.bound 2) (.bound 1) .newest))))))
    (Formula.forallMem C (Formula.forallMem D.weaken
      (.iff (entry_m (.bound 1) .newest F.weaken.weaken)
        (row_code_m α.weaken.weaken t.weaken.weaken (.bound 1) .newest))))
derive_free_closed row_map_m

theorem row_map_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α t C D F : Term n) :
    Formula.satisfies ρ (row_map_m α t C D F) ↔
      Row_map_d M (α.eval ρ) (t.eval ρ) (C.eval ρ) (D.eval ρ) (F.eval ρ) := by
  simp only [row_map_m, Row_map_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, kpair_sat_l M hE, Formula.satisfies_iff_iff,
    entry_sat_l M hE, row_code_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, fun c q hc hq => h.2 c hc q hq⟩, fun h => ⟨h.1, fun c hc q hq => h.2 c q hc hq⟩⟩

theorem Row_map_d.entry_l {α t C D F} (h : Row_map_d M α t C D F) (c q) :
    Entry_d M c q F ↔ M.mem c C ∧ M.mem q D ∧ Row_code_d M α t c q := by
  constructor
  · intro hcq
    obtain ⟨v, hv, hvF⟩ := hcq
    obtain ⟨c', q', hc, hq, hv'⟩ := h.1 v hvF
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    exact ⟨hc, hq, (h.2 _ _ hc hq).mp ⟨v, hv, hvF⟩⟩
  · rintro ⟨hc, hq, hcode⟩
    exact (h.2 c q hc hq).mpr hcode

theorem row_map_unique_l (hE : Extensional M) {α t C D F G}
    (h : Row_map_d M α t C D F) (k : Row_map_d M α t C D G) : F = G :=
  entry_ext_l M hE (fun v hv => (h.1 v hv).elim fun c hc => hc.elim fun q hq => ⟨c, q, hq.2.2⟩)
    (fun v hv => (k.1 v hv).elim fun c hc => hc.elim fun q hq => ⟨c, q, hq.2.2⟩)
    (fun c q => (h.entry_l c q).trans (k.entry_l c q).symm)

theorem smem_row_map_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c H J}
    (hM : Smdl_d I c H J) (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hH : M.TransitiveSet H) (α t C D F : (smdl_structure_l I (R := J) hM.2.1).Domain) :
    Row_map_d (smdl_structure_l I (R := J) hM.2.1) α t C D F ↔ Row_map_d M α.val t.val C.val D.val F.val := by
  let L := smdl_structure_l I (R := J) hM.2.1
  constructor
  · rintro ⟨hF, hf⟩
    refine ⟨fun v hv => ?_, fun c q hc hq => ?_⟩
    · let v' : L.Domain := ⟨v, hH F.val F.property v hv⟩
      obtain ⟨c, q, hc, hq, hv⟩ := hF v' ((smem_member_l I hM hJ v' F).mpr hv)
      exact ⟨c.val, q.val, (smem_member_l I hM hJ c C).mp hc, (smem_member_l I hM hJ q D).mp hq,
        (smem_kpair_l I hM hJ hH v' c q).mp hv⟩
    · let c' : L.Domain := ⟨c, hH C.val C.property c hc⟩
      let q' : L.Domain := ⟨q, hH D.val D.property q hq⟩
      exact (smem_entry_l I hM hJ hH c' q' F).symm.trans
        ((hf c' q' ((smem_member_l I hM hJ c' C).mpr hc) ((smem_member_l I hM hJ q' D).mpr hq)).trans
          (smem_row_code_l I hM hJ hH α t c' q'))
  · rintro ⟨hF, hf⟩
    refine ⟨fun v hv => ?_, fun c q hc hq => ?_⟩
    · obtain ⟨c, q, hc, hq, hv⟩ := hF v.val ((smem_member_l I hM hJ v F).mp hv)
      let c' : L.Domain := ⟨c, hH C.val C.property c hc⟩
      let q' : L.Domain := ⟨q, hH D.val D.property q hq⟩
      exact ⟨c', q', (smem_member_l I hM hJ c' C).mpr hc, (smem_member_l I hM hJ q' D).mpr hq,
        (smem_kpair_l I hM hJ hH v c' q').mpr hv⟩
    · exact (smem_entry_l I hM hJ hH c q F).trans
        ((hf c.val q.val ((smem_member_l I hM hJ c C).mp hc) ((smem_member_l I hM hJ q D).mp hq)).trans
          (smem_row_code_l I hM hJ hH α t c q).symm)

theorem selem_row_map_l (hZFC : M.Models ZFC) {ω χ H c J d N K α t C D F} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c d H J N K)
    (hElem : Selem_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω c d)
    (hα : M.mem α N) (ht : M.mem t N) (hC : M.mem C N) (hD : M.mem D N)
    (hF : Row_map_d M α t C D F) : M.mem F N := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  have htr := ZF.h_transitive_l I hZF hH
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I C D
  have hPH := h_product_l hZFC hω hχ hωχ hH (hSub.subset C hC) (hSub.subset D hD) hP
  have hFH := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hPH F (fun v hv => (hP v).mpr (by
    obtain ⟨c, q, hc, hq, hv⟩ := hF.1 v hv
    exact ⟨c, hc, q, hq, hv⟩))
  let L := smdl_structure_l I (R := J) hSub.source.2.1
  let Q := smdl_structure_l I (R := K) hSub.target.2.1
  let ρ₀ : Env L 1 := ⟨fun _ => ⟨α, hSub.subset α hα⟩, fun _ => ⟨α, hSub.subset α hα⟩⟩
  let ρ : Env L 4 := ((ρ₀.push ⟨t, hSub.subset t ht⟩).push ⟨C, hSub.subset C hC⟩).push ⟨D, hSub.subset D hD⟩
  let η : Env Q 4 := (((⟨fun _ => ⟨α, hα⟩, fun _ => ⟨α, hα⟩⟩ : Env Q 1).push ⟨t, ht⟩).push ⟨C, hC⟩).push ⟨D, hD⟩
  let φ : UnarySchema 4 := { body := row_map_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ (F : L.Domain) : φ.denote ρ F ↔ Row_map_d M α t C D F.val :=
    (row_map_sat_l (smem_ext_l I hSub.source hJ htr hZF.1) _ _ _ _ _ _).trans
      (smem_row_map_l I hSub.source hJ htr _ _ _ _ F)
  obtain ⟨F', hF'⟩ := selem_witness_l I hZF hω hSub hElem φ ρ η
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) ⟨⟨F, hFH⟩, (hφ _).mpr hF⟩
  exact (row_map_unique_l hZF.1 ((hφ _).mp hF') hF) ▸ F'.property

end YesMetaZFC.Model.Forcing.Internal
