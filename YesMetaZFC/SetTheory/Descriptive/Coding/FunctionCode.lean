import YesMetaZFC.Model.SetTheory.Internal.Theory

/-! # 可数值图的实数编码

由原内部单射读取实数坐标；逆图、复合及域外填充值实际构造编码。
供 Borel 证书和博弈策略共同使用，不依赖选择公理或外部标准性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Nv_d (E w a v : M.Domain) : Prop := ∃ i, M.PairMember I a i E ∧ M.PairMember I i v w
def nv_m {d} (E w a v : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 a.weaken .newest E.weaken) (Formula.orderedPairMem 𝒞 .newest v.weaken w.weaken))
derive_free_closed nv_m
theorem nv_sat_l {d} (ρ : Env M d) (E w a v : Term d) :
    Formula.satisfies ρ (nv_m (𝒞 := 𝒞) E w a v) ↔ Nv_d I (E.eval ρ) (w.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [nv_m, Nv_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem nv_unique_l {ω T E w a v u} (he : M.IsSetFunctionFromTo I E T ω) (hw : M.IsSetFunction I w)
    (h : Nv_d I E w a v) (k : Nv_d I E w a u) : v = u := by
  obtain ⟨i, hi, hv⟩ := h
  obtain ⟨j, hj, hu⟩ := k
  exact hw.2 i v u hv (he.1.2 a j i hj hi ▸ hu)

theorem nv_total_l {ω T E w a} (he : M.IsSetFunctionFromTo I E T ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) (ha : M.mem a T) : ∃ v, M.mem v ω ∧ Nv_d I E w a v := by
  obtain ⟨i, hi, hai⟩ := he.2.2 a ha
  obtain ⟨v, hv, hiv⟩ := hw.2.2 i hi
  exact ⟨v, hv, i, hai, hiv⟩

/-- 任意已编号的可数值图都能无选择地编码为实数。 -/
theorem nv_encode_l (hZF : M.Models ZF) {ω T E G z} (he : M.IsSetInjectionFromTo I E T ω)
    (hg : M.IsSetFunctionFromTo I G T ω) (hz : M.mem z ω) :
    ∃ w, M.IsSetFunctionFromTo I w ω ω ∧ ∀ a v, M.mem a T → (Nv_d I E w a v ↔ M.PairMember I a v G) := by
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I he.1.1 he.1.2.1
  have hd : M.IsSetBijectionFromTo I E T D :=
    ⟨⟨⟨he.1.1, he.1.2.1, fun a ha => (he.1.2.2 a ha).elim fun i h => ⟨i, (hD i).mpr ⟨a, h.2⟩, h.2⟩⟩, he.2⟩,
      fun i hi => ((hD i).mp hi).elim fun a h => ⟨a, he.1.input_mem_of_pairMember h, h⟩⟩
  obtain ⟨K, hk, ek⟩ := ZF.exists_inverseBijectionWithPairs hZF I hd
  obtain ⟨P, hp, ep⟩ := ZF.exists_compositionFunction hZF I hk.1.1 hg
  obtain ⟨w, ew, hw⟩ := Internal.senv_fill_exists_l I hZF (ω := ω) hp hz
  refine ⟨w, hw, fun a v ha => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hai, hiv⟩
    have hi := (hD i).mpr ⟨a, hai⟩
    have hiv := ((ew.2 i v).mp hiv).2.elim And.right (fun h => (h.1 hi).elim)
    obtain ⟨_, b, hib, hbv⟩ := (ep i v).mp hiv
    exact he.2 b a i ((ek i b).mp hib) hai ▸ hbv
  · intro hav
    obtain ⟨i, hiω, hai⟩ := he.1.2.2 a ha
    have hi := (hD i).mpr ⟨a, hai⟩
    exact ⟨i, hai, (ew.2 i v).mpr ⟨hiω, Or.inl ⟨hi, (ep i v).mpr ⟨hi, a, (ek i a).mpr hai, hav⟩⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive
