import YesMetaZFC.Model.SetTheory.Internal.RelationConstant

/-! # 逐点编译的实际解释环境

编译程序与模型无关。解释存在量词只需源中的常值函数；这里把这一
已由源理论构造的性质写成原公式，供同时量化所有模型的内部归纳使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_context_d (ω c X R D E : M.Domain) : Prop := Rf_ext_d I X R ∧ Smdl_d I c X R ∧
  M.IsFunctionSpace I E ω X ∧ M.mem D X ∧
  ∀ x, M.mem x X → ∃ f, Rf_fun_d I X R D f ∧
    ∀ v, M.mem v X → M.PairMember I v D R → Rf_val_d I X R v x f

def pe_context_m {d} (ω c X R D E : Term d) : Formula 1 d :=
  .conj (rf_ext_m (𝒞 := 𝒞) X R) (.conj (smdl_m (𝒞 := 𝒞) c X R)
    (.conj (Formula.isFunctionSpace 𝒞 E ω X) (.conj (.mem D X)
      (Formula.forallMem X (.existsE (.conj
        (rf_fun_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken D.weaken.weaken .newest)
        (Formula.forallMem X.weaken.weaken (.imp
          (Formula.orderedPairMem 𝒞 .newest D.weaken.weaken.weaken R.weaken.weaken.weaken)
          (rf_val_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken .newest (.bound 2) (.bound 1))))))))))

@[simp] theorem pe_context_closed_l {d} (ω c X R D E : Term d)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hD : D.freeSupport = []) (hE : E.freeSupport = []) :
    (pe_context_m (𝒞 := 𝒞) ω c X R D E).FreeClosed := by
  simp -implicitDefEqProofs [pe_context_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hc, hX, hR, hD, hE]

theorem pe_context_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X R D E : Term d) :
    Formula.satisfies ρ (pe_context_m (𝒞 := 𝒞) ω c X R D E) ↔
      Pe_context_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) (D.eval ρ) (E.eval ρ) := by
  simp only [pe_context_m, Pe_context_d, Formula.satisfies_conj_iff, rf_ext_sat_l I hE,
    smdl_sat_l I, Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, rf_fun_sat_l I, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    rf_val_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem sc_pe_context_l (hZF : M.Models ZF) {ω c X R D E : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hD : M.mem D X) (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E ω X) :
    Pe_context_d (kp_pair_l (ZF.modelsKP hZF)) ω c X R D E := by
  refine ⟨rf_ext_mem_l _ hZF.1 hX hm, hm.1, hE, hD, fun x hx => ?_⟩
  obtain ⟨f, C, hf, hC, hg, hs⟩ := sc_constant_l hZF hω hX hm theory hD hx
  exact ⟨f, (rf_fun_mem_l _ hZF.1 hX hm hD).mpr ⟨hf, C, hC, hg⟩, fun v _ hv =>
    (rf_val_mem_l _ hZF.1 hX hm hf).mpr ((hs v x).mpr ⟨((hm.2 v D).mp hv).2.2, rfl⟩)⟩

section
variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 原始关系像的实际解释环境；全部新对象的常值函数由封闭句子取得。 -/
theorem Smap_d.pe_context_l {ω c X R c' Y S q D E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d Q c X R)
    (theory : Sc_theory_d Q ω X R) (model : Smdl_d Q c' Y S) (hq : Smap_d Q ω c c' X Y q)
    (hD : M.mem D Y) (hE : M.IsFunctionSpace Q E ω Y) : Pe_context_d Q ω c' Y S D E := by
  have ext : Rf_ext_d Q Y S := hq.extensional_l hZF hω hm.1 model (rf_ext_mem_l Q hZF.1 hX hm)
  have en := ext.native_l Q model.2.1
  refine ⟨ext, model, hE, hD, fun x hx => ?_⟩
  obtain ⟨B, f, fn, val⟩ := sc_constant_raw_l hZF hω hX hm theory model hq en ⟨D, hD⟩ ⟨x, hx⟩
  exact ⟨f.val, (rf_fun_native_l Q model.2.1 en ⟨D, hD⟩ f).mpr ⟨B, fn⟩, fun v hv hd =>
    (rf_val_native_l Q model.2.1 en ⟨v, hv⟩ ⟨x, hx⟩ f).mpr (val ⟨v, hv⟩ hd)⟩
end

end YesMetaZFC.SetTheory.Internal
