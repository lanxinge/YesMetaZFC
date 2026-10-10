import YesMetaZFC.Model.SetTheory.Internal.ProgramRecode
import YesMetaZFC.Model.SetTheory.Internal.Induction
import YesMetaZFC.Model.SetTheory.Internal.Satisfaction

/-! # 更换程序编码保持全部内部公式的真值

对原程序作内部强归纳。存在量词在两种赋值编码上同时更新同一个坐标，
因此并非只证明无量词片段或外部标准公式的保持性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 𝒟 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) (J : 𝒟.Interpretation M)

def Sx_graph_d (F G : M.Domain) : Prop := ∀ x y, M.PairMember J x y G ↔ M.PairMember I x y F

def sx_graph_m {n} (F G : Term n) : Formula 1 n := set[n] ⟪∀ x y,
  (⌜Formula.orderedPairMem 𝒟⌝ₚ(x, y, ⌜G⌝ₛ) ↔ ⌜Formula.orderedPairMem 𝒞⌝ₚ(x, y, ⌜F⌝ₛ))⟫
derive_free_closed sx_graph_m

theorem sx_graph_sat_l {n} (ρ : Env M n) (F G : Term n) :
    Formula.satisfies ρ (sx_graph_m (𝒞 := 𝒞) (𝒟 := 𝒟) F G) ↔ Sx_graph_d I J (F.eval ρ) (G.eval ρ) := by
  simp only [sx_graph_m, Sx_graph_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_orderedPairMem_iff J, Definitional.Term.eval_weaken]; rfl

theorem Sx_graph_d.update_l {f g i x a b} (h : Sx_graph_d I J f g)
    (ha : Senv_update_d I f i x a) (hb : Senv_update_d J g i x b) : Sx_graph_d I J a b :=
  fun j y => (hb.2 j y).trans ((or_congr Iff.rfl (and_congr Iff.rfl (h j y))).trans (ha.2 j y).symm)

def Sx_row_d (X R S E D F G n r : M.Domain) : Prop := ∀ f g,
  M.mem f E → M.mem g D → Sx_graph_d I J f g →
    (Ssat_d I X R E F n r f ↔ Ssat_d J X S D G n r g)

def sx_row_m {d} (X R S E D F G n r : Term d) : Formula 1 d := set[d] ⟪∀ f g,
  f ∈ ⌜E⌝ₛ → g ∈ ⌜D⌝ₛ → ⌜sx_graph_m (𝒞 := 𝒞) (𝒟 := 𝒟)⌝ₚ(f, g) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜E⌝ₛ, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, f) ↔
      ⌜ssat_m (𝒞 := 𝒟)⌝ₚ(⌜X⌝ₛ, ⌜S⌝ₛ, ⌜D⌝ₛ, ⌜G⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, g))⟫
derive_free_closed sx_row_m

theorem sx_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R S E D F G n r : Term d) :
    Formula.satisfies ρ (sx_row_m (𝒞 := 𝒞) (𝒟 := 𝒟) X R S E D F G n r) ↔
      Sx_row_d I J (X.eval ρ) (R.eval ρ) (S.eval ρ) (E.eval ρ) (D.eval ρ)
        (F.eval ρ) (G.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [sx_row_m, Sx_row_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, sx_graph_sat_l I J, Formula.satisfies_iff_iff,
    ssat_sat_l I hE, ssat_sat_l J hE, Definitional.Term.eval_weaken]; rfl

theorem Sx_program_d.correct_l (hZF : M.Models ZF) {ω X R S E D F G n r}
    (h : Sx_program_d I J F G) (hf : Sfm_d I ω n F)
    (he : M.IsFunctionSpace I E ω X) (hd : M.IsFunctionSpace J D ω X)
    (rel : Sx_graph_d I J R S) (hr : M.mem r n) : Sx_row_d I J X R S E D F G n r := by
  have hg := h.program_l I J hf
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hf.2.1.1
  obtain ⟨K, hK⟩ := seval_exists_l J hZF X S D G hg.2.1.1
  let ρ : Env M 8 := ⟨Fin.cases n (Fin.cases G (Fin.cases F (Fin.cases D
    (Fin.cases E (Fin.cases S (Fin.cases R (fun _ => X))))))), fun _ => X⟩
  let φ : UnarySchema 8 := { body := (sx_row_m (𝒞 := 𝒞) (𝒟 := 𝒟)
    (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have sat k : φ.denote ρ k ↔ Sx_row_d I J X R S E D F G n k := by
    simp only [φ, UnarySchema.denote, sx_row_sat_l I J hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l I hZF hf φ ρ ?_ hr)
  intro r hr ih
  apply (sat r).mpr
  intro f g hfE hgD agree
  have ff := (he f).mp hfE
  have gg := (hd g).mp hgD
  obtain ⟨c, hc⟩ := (hf.2.1.2.2 r).mp hr
  obtain ⟨d, hdG⟩ := (hg.2.1.2.2 r).mp hr
  have node := h.row_l I J hf.2.1.2.1 hc hdG
  rcases hf.2.2 r c hc with ⟨i, j, op, hi, hj⟩ | ⟨i, j, op, hi, hj⟩ |
    ⟨i, j, op, hi, hj⟩ | ⟨i, j, op, hi, hj⟩
  · obtain ⟨x, _, hix⟩ := ff.2.2 i hi
    obtain ⟨y, _, hjy⟩ := ff.2.2 j hj
    exact (ssat_rel_l I hZF hf hH hc op he hfE hix hjy).trans ((rel x y).symm.trans
      (ssat_rel_l J hZF hg hK hdG (node.op_l I J op) hd hgD ((agree i x).mpr hix) ((agree j y).mpr hjy)).symm)
  · obtain ⟨x, _, hix⟩ := ff.2.2 i hi
    obtain ⟨y, _, hjy⟩ := ff.2.2 j hj
    exact (ssat_eq_l I hZF hf hH hc op he hfE hix hjy).trans
      (ssat_eq_l J hZF hg hK hdG (node.op_l I J op) hd hgD ((agree i x).mpr hix) ((agree j y).mpr hjy)).symm
  · rw [ssat_nor_l I hZF hf hH hc op hfE, ssat_nor_l J hZF hg hK hdG (node.op_l I J op) hgD]
    exact not_congr (or_congr ((sat i).mp (ih i hi) f g hfE hgD agree) ((sat j).mp (ih j hj) f g hfE hgD agree))
  · have tr x a b (hx : M.mem x X) (ha : Senv_update_d I f i x a) (hb : Senv_update_d J g i x b) :
        Ssat_d I X R E F n j a ↔ Ssat_d J X S D G n j b :=
      (sat j).mp (ih j hj) a b ((he a).mpr (ha.function_l I ff hi hx))
        ((hd b).mpr (hb.function_l J gg hi hx)) (agree.update_l I J ha hb)
    rw [ssat_exists_l I hZF hf hH hc op hfE, ssat_exists_l J hZF hg hK hdG (node.op_l I J op) hgD]
    constructor
    · rintro ⟨x, a, hx, ha, truth⟩
      obtain ⟨b, hb, _⟩ := senv_update_exists_l J hZF gg hi hx
      exact ⟨x, b, hx, hb, (tr x a b hx ha hb).mp truth⟩
    · rintro ⟨x, b, hx, hb, truth⟩
      obtain ⟨a, ha, _⟩ := senv_update_exists_l I hZF ff hi hx
      exact ⟨x, a, hx, ha, (tr x a b hx ha hb).mpr truth⟩

/-- 两种实际隶属结构和对应赋值读出相同的完整满足关系。 -/
theorem Sx_program_d.satisfies_l (hZF : M.Models ZF) {ω X R S c d a b F G n r f g}
    (h : Sx_program_d I J F G) (hc : Smem_d I c X R) (hd : Smem_d J d X S)
    (ha : Sformula_d I ω a n F r) (hb : J.Codes b G r)
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo J g ω X)
    (agree : Sx_graph_d I J f g) : Satisfies_d I ω c a f ↔ Satisfies_d J ω d b g := by
  obtain ⟨E, he, _⟩ := senv_space_l I hZF ω hc.1.2.1
  obtain ⟨D, hD, _⟩ := senv_space_l J hZF ω hd.1.2.1
  have hb' : Sformula_d J ω b n G r := ⟨hb, h.program_l I J ha.2.1, ha.2.2⟩
  exact (satisfies_decode_l I hZF.1 hc.1 ha he).trans
    ((h.correct_l I J hZF ha.2.1 he hD (fun x y => (hd.2 x y).trans (hc.2 x y).symm) ha.2.2
      f g ((he f).mpr hf) ((hD g).mpr hg) agree).trans (satisfies_decode_l J hZF.1 hd.1 hb' hD).symm)

end YesMetaZFC.SetTheory.Internal
