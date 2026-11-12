import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.TarskiVaughtSyntax
import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.Model.SetTheory.Embedding.ElementarySyntax
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource

/-! # 从有限参数司寇伦闭性到完整内部见证闭性

把任意赋值限制到程序的内部有限坐标界，再按基点延拓。真值一致性允许在该
有限参数列上选择见证，随后把见证搬回原完整赋值。整个转换只需 ZF。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssk_full_l (hZF : M.Models ZF) {ω c X R u C N} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hC : Scode_d I ω C) (hN : M.MemberSubset N X) (hu : M.mem u N)
    (hs : Ssk_closed_d I ω c X u C N) : Stv_d I ω c X C N := by
  rintro a i f ha hi hf ⟨x, g, hx, hg, ht⟩
  obtain ⟨n, F, k, hCode⟩ := (hC a).mp ha
  obtain ⟨b, hb, hBound⟩ := sbound_exists_l I hZF hω hCode.2.1
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have agree {p q} (hp : M.IsSetFunctionFromTo I p ω X) (hq : M.IsSetFunctionFromTo I q ω X)
      (he : Senv_agree_d I b p q) : Satisfies_d I ω c a p ↔ Satisfies_d I ω c a q :=
    (satisfies_decode_l I hZF.1 hM hCode hE).trans
      ((ssat_agree_l I hZF hCode.2.1 hBound hE hCode.2.2 ((hE p).mpr hp) ((hE q).mpr hq) he).trans
        (satisfies_decode_l I hZF.1 hM hCode hE).symm)
  obtain ⟨s, hRestr⟩ := ZF.exists_restriction hZF I f b
  have hbw := hω.transitive (ZF.modelsKP hZF) b hb
  have hsN := hRestr.isSetFunctionFromTo hf hbw
  obtain ⟨f₀, hFill, hf₀⟩ := senv_fill_exists_l I hZF (ω := ω) hsN hu
  have he := senv_fill_agree_l I hbw hRestr hFill
  have hfX := hf.mono_target_l I hN
  have hf₀X := hf₀.mono_target_l I hN
  obtain ⟨g₀, hg₀, hG₀⟩ := senv_update_exists_l I hZF hf₀X hi hx
  have ht₀ := (agree (hg.function_l I hfX hi hx) hG₀ (he.update_l I hg hg₀)).mp ht
  obtain ⟨y, hy, hys⟩ := hs a i b s ha hi hb hsN
    ⟨x, hx, b, f₀, g₀, hb, hsN.mono_target_l I hN, hFill, hg₀, ht₀⟩
  obtain ⟨q₀, hq₀, hQ₀⟩ := senv_update_exists_l I hZF hf₀ hi hy
  have hyt := (ssk_wit_decode_l I hZF.1 hb (hsN.mono_target_l I hN) hFill hq₀).mp hys
  obtain ⟨q, hq, hQ⟩ := senv_update_exists_l I hZF hf hi hy
  exact ⟨y, q, hy, hq,
    (agree (hQ.mono_target_l I hN) (hQ₀.mono_target_l I hN) (he.update_l I hq hq₀)).mpr hyt⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部 Tarski–Vaught 定理

对实际内部程序作原公式强归纳，同时比较大结构与限制结构的真值表。存在量词
使用完整赋值上的见证回拉；反向把内部存在指令追加到任意合法程序。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssat_submodel_l (hZF : M.Models ZF) {ω c d X R N S C E D F n k f}
    (hS : Ssub_d I c d X R N S) (hC : Scode_d I ω C) (hTV : Stv_d I ω c X C N)
    (hF : Sfm_d I ω n F) (hE : M.IsFunctionSpace I E ω X) (hD : M.IsFunctionSpace I D ω N)
    (hk : M.mem k n) (hf : M.mem f D) : Ssat_d I X R E F n k f ↔ Ssat_d I N S D F n k f := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF N S D F hF.2.1.1
  have large {f} (hf : M.mem f D) : M.mem f E := (hE f).mpr (((hD f).mp hf).mono_target_l I hS.subset)
  let ρ : Env M 8 := (((((((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push E).push N).push S).push D).push F).push n
  let φ : UnarySchema 8 := {
    body := Formula.forallMem (.bound 3) (.iff
      (ssat_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 3) (.bound 2) (.bound 1) .newest)
      (ssat_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)) }
  have hφ r : φ.denote ρ r ↔ ∀ f, M.mem f D →
      (Ssat_d I X R E F n r f ↔ Ssat_d I N S D F n r f) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, ssat_sat_l I hZF.1]
    rfl
  suffices hh : φ.denote ρ k from (hφ k).mp hh f hf
  apply sfm_induction_l I hZF hF φ ρ ?_ hk
  intro r hr ih
  apply (hφ r).mpr
  intro f hf
  have hfE := large hf
  obtain ⟨a, ha⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r a ha with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨x, hx, hix⟩ := ((hD f).mp hf).2.2 i hi
    obtain ⟨y, hy, hjy⟩ := ((hD f).mp hf).2.2 j hj
    have rel : M.PairMember I x y R ↔ M.PairMember I x y S :=
      ⟨fun h => (hS.relation x y).mpr ⟨hx, hy, h⟩, fun h => ((hS.relation x y).mp h).2.2⟩
    exact (ssat_rel_l I hZF hF hH ha hs hE hfE hix hjy).trans
      (rel.trans (ssat_rel_l I hZF hF hJ ha hs hD hf hix hjy).symm)
  · obtain ⟨x, _, hix⟩ := ((hD f).mp hf).2.2 i hi
    obtain ⟨y, _, hjy⟩ := ((hD f).mp hf).2.2 j hj
    exact (ssat_eq_l I hZF hF hH ha hs hE hfE hix hjy).trans
      (ssat_eq_l I hZF hF hJ ha hs hD hf hix hjy).symm
  · rw [ssat_nor_l I hZF hF hH ha hs hfE, ssat_nor_l I hZF hF hJ ha hs hf]
    exact not_congr (or_congr ((hφ i).mp (ih i hi) f hf) ((hφ j).mp (ih j hj) f hf))
  · rw [ssat_exists_l I hZF hF hH ha hs hfE, ssat_exists_l I hZF hF hJ ha hs hf]
    constructor
    · rintro ⟨x, g, hx, hg, ht⟩
      obtain ⟨b, hb⟩ := I.total F j
      have hB : Sformula_d I ω b n F j := ⟨hb, hF, hF.2.1.1.transitive r hr j hj⟩
      obtain ⟨y, h, hy, hh, ht⟩ := hTV b i f ((hC b).mpr ⟨n, F, j, hB⟩) hi ((hD f).mp hf)
        ⟨x, g, hx, hg, (satisfies_decode_l I hZF.1 hS.source hB hE).mpr ht⟩
      have hhD := (hD h).mpr (hh.function_l I ((hD f).mp hf) hi hy)
      exact ⟨y, h, hy, hh, ((hφ j).mp (ih j hj) h hhD).mp
        ((satisfies_decode_l I hZF.1 hS.source hB hE).mp ht)⟩
    · rintro ⟨x, g, hx, hg, ht⟩
      have hgD := (hD g).mpr (hg.function_l I ((hD f).mp hf) hi hx)
      exact ⟨x, g, hS.subset x hx, hg, ((hφ j).mp (ih j hj) g hgD).mpr ht⟩

/-- 完整内部见证回拉蕴含全部内部公式、全部内部赋值下的初等性。 -/
theorem selem_of_tv_l (hZF : M.Models ZF) {ω c d X R N S C}
    (hS : Ssub_d I c d X R N S) (hC : Scode_d I ω C) (hTV : Stv_d I ω c X C N) : Selem_d I ω c d := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω N
  apply (selem_decode_l I hZF.1 hS hC).mpr
  intro a f ha hf
  obtain ⟨n, F, k, hk⟩ := (hC a).mp ha
  exact (satisfies_decode_l I hZF.1 hS.source hk hE).trans
    ((ssat_submodel_l I hZF hS hC hTV hk.2.1 hE hD hk.2.2 ((hD f).mpr hf)).trans
      (satisfies_decode_l I hZF.1 hS.target hk hD).symm)

/-- 初等性反过来给出内部见证回拉；使用实际追加的存在指令。 -/
theorem stv_of_selem_l (hZF : M.Models ZF) {ω c d X R N S C} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (hC : Scode_d I ω C) (he : Selem_d I ω c d) : Stv_d I ω c X C N := by
  have elem := (selem_decode_l I hZF.1 hS hC).mp he
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω N
  rintro a i f ha hi hf ⟨x, g, hx, hg, ht⟩
  obtain ⟨n, F, k, hA⟩ := (hC a).mp ha
  obtain ⟨m, G, r, hb, hex⟩ := sfm_ex_l I hZF hω hA.2.1 hi hA.2.2
  obtain ⟨b, hbr⟩ := I.total G r
  have hB : Sformula_d I ω b m G r := ⟨hbr, hb.program, hb.root⟩
  have hTrue := (hex X R E f ((hE f).mpr (hf.mono_target_l I hS.subset))).mpr
    ⟨x, g, hx, hg, (satisfies_decode_l I hZF.1 hS.source hA hE).mp ht⟩
  have hSmall := (satisfies_decode_l I hZF.1 hS.target hB hD).mp
    ((elem b f ((hC b).mpr ⟨m, G, r, hB⟩) hf).mp ((satisfies_decode_l I hZF.1 hS.source hB hE).mpr hTrue))
  obtain ⟨y, h, hy, hh, hs⟩ := (hex N S D f ((hD f).mpr hf)).mp hSmall
  have hFn := hh.function_l I hf hi hy
  exact ⟨y, h, hy, hh, (elem a h ha hFn).mpr ((satisfies_decode_l I hZF.1 hS.target hA hD).mpr hs)⟩

theorem selem_iff_tv_l (hZF : M.Models ZF) {ω c d X R N S C} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (hC : Scode_d I ω C) : Selem_d I ω c d ↔ Stv_d I ω c X C N :=
  ⟨stv_of_selem_l I hZF hω hS hC, selem_of_tv_l I hZF hS hC⟩

end YesMetaZFC.SetTheory.Internal
