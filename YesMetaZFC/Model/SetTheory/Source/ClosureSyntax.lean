import YesMetaZFC.Model.SetTheory.Source.FinitePartial
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Relations.Collection
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis
import YesMetaZFC.SetTheory.HereditarySequences
import YesMetaZFC.Model.SetTheory.LevyReflection.Decode
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 原关系中的指定有限序列空间

自然数对象、字母表和整个有限空间均为原模型的对象码。
实际隶属实例由配对与并集回收所有背景内部有限图，包含非标准长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def sc_fseq0_m {d} (w A K : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest K.weaken)
    (Formula.existsMem w.weaken (fn0_m .newest A.weaken.weaken (.bound 1))))

derive_free_closed sc_fseq0_m

def Sc_fseq_d (w A K X R : M.Domain) : Prop :=
  Rr_truth_d I (n := 2) X R (sc_fseq0_m (.bound 2) (.bound 1) .newest)
    (Fin.cases K (Fin.cases A (fun _ => w)))

theorem Sc_fseq_d.bounds_l {w A K X R : M.Domain} (h : Sc_fseq_d I w A K X R) :
    M.mem w X ∧ M.mem A X ∧ M.mem K X := by
  obtain ⟨b, _⟩ := h
  exact ⟨b 2, b 1, b 0⟩

theorem Sc_fseq_d.mem_l {J : 𝒞.Interpretation M} {w A K X R : M.Domain}
    (h : Sc_fseq_d J w A K X R) : M.mem K X := (h.bounds_l J).2.2

theorem sc_fseq_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (w A K : (smdl_structure_l I (R := R) nx).Domain) :
    Sc_fseq_d I w.val A.val K.val X R ↔
      ∀ f : (smdl_structure_l I (R := R) nx).Domain,
        (smdl_structure_l I (R := R) nx).mem f K ↔
          ∃ n, (smdl_structure_l I (R := R) nx).mem n w ∧ Fn0_d n A f := by
  let v : Fin 3 → (smdl_structure_l I (R := R) nx).Domain := Fin.cases K (Fin.cases A (fun _ => w))
  have values : (fun i => (v i).val) = Fin.cases K.val (Fin.cases A.val (fun _ => w.val)) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  change Rr_truth_d I X R (sc_fseq0_m (d := 3) (.bound 2) (.bound 1) .newest) _ ↔ _
  rw [← values, rr_truth_native_l I nx _ (by simp -implicitDefEqProofs) v]
  simp only [sc_fseq0_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn0_sat_l ext, Definitional.Term.eval_weaken]
  rfl

/-- 字面有限空间的完整性由有限图闭包保证，不把宿主有限性当作模型内有限性。 -/
theorem sc_fseq_mem_l (hKP : M.Models KP) {ω c A K X R : M.Domain}
    (hω : M.IsOmega ω) (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    (hw : M.mem ω X) (hA : M.mem A X) (hK : M.mem K X)
    (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (union : ∀ a, M.mem a X → ∃ b, M.mem b X ∧ M.IsUnionOf b a) :
    Sc_fseq_d I ω A K X R ↔ Fseq_space_d (kp_pair_l hKP) ω A K := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hw⟩⟩
  let N := rt_model_l X nx
  let ρ : Env N 3 := ⟨Fin.cases ⟨K, hK⟩ (Fin.cases ⟨A, hA⟩ (fun _ => ⟨ω, hw⟩)), fun _ => ⟨K, hK⟩⟩
  have values : (fun i => (ρ.bound i).val) = Fin.cases K (Fin.cases A (fun _ => ω)) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have read := (rr_truth_native_l I model.1.2.1 (sc_fseq0_m (d := 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ.bound).trans
      (smem_formula_l I model nx (sc_fseq0_m (.bound 2) (.bound 1) .newest) ρ).symm
  rw [values] at read
  change Sc_fseq_d I ω A K X R ↔ Formula.satisfies ρ _ at read
  have fn {d} (η : Env N d) (a b f : Term d) : Formula.satisfies η (fn0_m a b f) ↔
      Fn0_d (a.eval η).val (b.eval η).val (f.eval η).val := by
    have tr := (rt_model_delta_l trans nx (fn0_delta_l a b f) η).trans (fn0_sat_l hKP.1 ..)
    simpa only [eval_image_env_l (M := N) (N := M) Subtype.val] using tr
  rw [read]
  simp only [sc_fseq0_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn, Definitional.Term.eval_weaken]
  change (∀ f : N.Domain, M.mem f.val K ↔ ∃ n : N.Domain, M.mem n.val ω ∧ Fn0_d n.val A f.val) ↔ _
  constructor
  · intro h f
    constructor
    · intro hf
      obtain ⟨n, hn, fn⟩ := (h ⟨f, trans K hK f hf⟩).mp hf
      exact ⟨n.val, hn, fn0_function_l hKP fn⟩
    · rintro ⟨n, hn, fn⟩
      have fn := fn0_of_function_l hKP fn
      have hf := sc_finite_function_l hKP hω trans pair union hw (trans A hA) hn fn
      exact (h ⟨f, hf⟩).mpr ⟨⟨n, trans ω hw n hn⟩, hn, fn⟩
  · intro h f
    exact (h f.val).trans ⟨fun ⟨n, hn, fn⟩ => ⟨⟨n, trans ω hw n hn⟩, hn, fn0_of_function_l hKP fn⟩,
      fun ⟨n, hn, fn⟩ => ⟨n.val, hn, fn0_function_l hKP fn⟩⟩

def sc_fseq_m {d} (w A K X R : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (n := 2) (sc_fseq0_m (.bound 2) (.bound 1) .newest) X R
    (Fin.cases K (Fin.cases A (fun _ => w)))

@[simp] theorem sc_fseq_closed_l {d} (w A K X R : Term d)
    (hw : w.freeSupport = []) (ha : A.freeSupport = []) (hk : K.freeSupport = [])
    (hx : X.freeSupport = []) (hr : R.freeSupport = []) : (sc_fseq_m (𝒞 := 𝒞) w A K X R).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) X R _ hx hr (Fin.cases hk (Fin.cases ha (fun _ => hw)))

theorem sc_fseq_sat_l {d} (ρ : Env M d) (w A K X R : Term d) :
    Formula.satisfies ρ (sc_fseq_m (𝒞 := 𝒞) w A K X R) ↔
      Sc_fseq_d I (w.eval ρ) (A.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  let v : Fin 3 → Term d := Fin.cases K (Fin.cases A (fun _ => w))
  have values : (fun i => (v i).eval ρ) = Fin.cases (K.eval ρ) (Fin.cases (A.eval ρ) (fun _ => w.eval ρ)) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have read := rr_truth_sat_l I ρ (sc_fseq0_m (d := 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) X R v
  rw [values] at read
  exact read

end YesMetaZFC.SetTheory.Internal

/-! ## 小定义域收集的原关系保持与实际初值

小性、子集和函数见证均沿完整初等图传输。正则 Hχ 与正则极限 Vδ
继续由遗传大小闭包和共尾度秩界给出实例；不要求强极限或原生 ZFC。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sc_collection_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (source : Sc_collection_d I ω X R)
    (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S)
    (ex : Extensional (smdl_structure_l I (R := R) hm.2.1))
    (ey : Extensional (smdl_structure_l I (R := S) hn.2.1)) (hq : Smap_d I ω c d X Y q) :
    Sc_collection_d I ω Y S := (sc_collection_iff_l I hZF hω hm hn ex ey hq).mp source

theorem Sc_collection_d.pull_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (target : Sc_collection_d I ω Y S)
    (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S)
    (ex : Extensional (smdl_structure_l I (R := R) hm.2.1))
    (ey : Extensional (smdl_structure_l I (R := S) hn.2.1)) (hq : Smap_d I ω c d X Y q) :
    Sc_collection_d I ω X R := (sc_collection_iff_l I hZF hω hm hn ex ey hq).mpr target

section Pull
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 源内的实际小集合从目标收集回拉；只有字面读取端需要传递性。 -/
theorem smap_uniform_l {ω c d X R H S q E F n r i j f D} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smdl_d I d H S)
    (ey : Extensional (smdl_structure_l I (R := S) hn.2.1)) (hq : Smap_d I ω c d X H q)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hf : M.mem f E) (hD : M.mem D X)
    (small : Rf_small_d I X R D) (target : Sc_collection_d I ω H S)
    (hh : Scollect_d I X R E F n r i j f D X) :
    ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B := by
  have source := target.pull_l I hZF hω hm.1 hn (smem_ext_l I hm.1 hm.2 hX hZF.1) ey hq
  have uniform := source.uniform_l I small
  exact (sc_uniform_mem_l I hZF.1 hX hm hD).mp uniform E F n r i j f D hE hF hr hi hj hij hf hD (fun _ h => h) hh
end Pull

theorem sc_h_collection_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) (R : M.Domain)
    {c : M.Domain} (model : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c H R) :
    Sc_collection_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := ZF.h_transitive_l I hZF hH
  apply (sc_collection_mem_l I (ZF.modelsKP hZF) trans model).mpr
  intro D hD _
  apply (sc_uniform_mem_l I hZF.1 trans model hD).mpr
  intro E F n r i j f A _ _ _ _ _ _ _ hA _ total
  exact h_uniform_l hZFC hω hχ hωχ hH hA total

theorem sc_v_collection_l (hZFC : M.Models ZFC) {δ V : M.Domain}
    (hδ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) (ω R : M.Domain)
    {c : M.Domain} (model : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c V R) :
    Sc_collection_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := v_transitive_l I hV
  apply (sc_collection_mem_l I (ZF.modelsKP hZF) trans model).mpr
  intro D hD small
  apply (sc_uniform_mem_l I hZF.1 trans model hD).mpr
  intro E F n r i j f A _ _ _ _ _ _ _ hA hAD total
  obtain ⟨μ, e, hμ, _, index⟩ := small.mono_l hAD
  let ρ : Env M 9 := ⟨Fin.cases f (Fin.cases j (Fin.cases i (Fin.cases r (Fin.cases n
    (Fin.cases F (Fin.cases E (Fin.cases R (fun _ => V)))))))), fun _ => V⟩
  let φ : BinarySchema 9 := {
    body := sbin_m (𝒞 := kpair_convention_l) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat x y : φ.denote ρ x y ↔ Sbin_d I V R E F n r i j f x y := sbin_sat_l I hZF.1 ..
  obtain ⟨q, hq, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := A) (Y := V)
    (fun x hx => (total x hx).imp fun y hy => ⟨hy.1, (sat x y).mpr hy.2⟩)
  obtain ⟨C, hC, hf, hqV⟩ := ZF.v_small_function_l hZF hδ
    (ZF.v_ordinal_height_l hZF hV index.ordinal hμ) (index.bound_l (ZF.modelsKP hZF)) hA hV hq
  exact ⟨q, C, hqV, hC, fn0_of_function_l (ZF.modelsKP hZF) hf, fun x y hxy => (sat x y).mp (select x y hxy)⟩
end YesMetaZFC.SetTheory.Internal

/-! ## 原关系小集合收集的完整历史编码

程序码及赋值仍量化背景中的全部内部对象；小性、定义域成员和见证函数
都在同一原关系中解释。编码读取只需两侧外延性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

@[simp] private theorem sc_space_closed_l {d} (E ω X : Term d)
    (he : E.freeSupport = []) (hw : ω.freeSupport = []) (hx : X.freeSupport = []) :
    (Formula.isFunctionSpace kpair_convention_l E ω X).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isFunctionSpace, Definitional.Formula.FreeClosed, he, hw, hx]

def sc_uniform0_m {d} (Ω X R A : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i j f,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜Ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜Ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜Ω⌝ₛ → j ∈ ⌜Ω⌝ₛ → i ≠ j → f ∈ E →
    (∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, ⌜A⌝ₛ, ⌜R⌝ₛ) →
      ∃ y ∈ ⌜X⌝ₛ, ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y)) →
    ∃ B, ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜A⌝ₛ, B) ∧
      (∀ x y, ⌜rf_val_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, x, y, B) →
        ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y))⟫
derive_free_closed sc_uniform0_m

def sc_collection0_m {d} (Ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ A ∈ ⌜X⌝ₛ, ⌜rf_small_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, A) →
    ⌜sc_uniform0_m⌝ₚ(⌜Ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, A)⟫
derive_free_closed sc_collection0_m

/-- 同一原关系的全部小定义域与全部内部程序均由历史公式精确保存。 -/
theorem sc_collection0_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (Ω X R : Term d) (ext : Rf_ext_d I (X.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (sc_collection0_m Ω X R) ↔ Sc_collection_d I (Ω.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [sc_collection0_m, sc_uniform0_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    sfm_sat_l I hE, Formula.satisfies_mem_iff, Formula.extensionalNe,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, sbin_sat_l I hE, rf_small_sat_l I,
    rf_fun_sat_l I, rf_val_sat_l I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · intro h nx D μ e index ny E F n r i j f A hE hF hr hi hj hij hf hA sub total
    have small := (Rf_small_d.of_index_l I nx D μ e index).mono_l I hA sub
    obtain ⟨B, funB, select⟩ := h A hA small E F n r i j f hE hF hr hi hj hij hf total
    obtain ⟨_, hB, C, valid⟩ := funB
    have fn : Fn0_d (⟨A, hA⟩ : (smdl_structure_l I (R := R.eval ρ) ny).Domain) C ⟨B, hB⟩ :=
      (fn0_sat_l (ext.native_l I ny) ..).mp valid
    exact ⟨⟨B, hB⟩, C, fn, fun x y hxy =>
      select x.val y.val ((rf_val_native_l I ny (ext.native_l I ny) x y ⟨B, hB⟩).mpr hxy)⟩
  · intro h A hA small E F n r i j f hE hF hr hi hj hij hf total
    let nx : ∃ x, M.mem x (X.eval ρ) := ⟨A, hA⟩
    obtain ⟨B, C, fn, select⟩ := h.uniform_l I small nx E F n r i j f A hE hF hr hi hj hij hf hA
      (fun _ _ h => h) total
    refine ⟨B.val, (rf_fun_native_l I nx (ext.native_l I nx) ⟨A, hA⟩ B).mpr ⟨C, fn⟩, ?_⟩
    intro x y value
    obtain ⟨hx, hy, hB, valid⟩ := value
    exact select ⟨x, hx⟩ ⟨y, hy⟩ ((rd_entry0_sat_l (ext.native_l I nx) ..).mp valid)

end YesMetaZFC.SetTheory.Internal

/-! ## 有限序列空间在后继模型中的实际保持

全部字母表的有限列空间与编号合并为原关系中的一个全称句子。
自然数对象作为参数沿实际初等图取像。仅在传递隶属实例中，有限函数闭性
把该句子读为包含全部背景内部有限图的实际空间；目标的新字母表同样受控。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_seq_index_m {n} (ω A K : Term n) : Formula 1 n := .forallE (.forallE
  (.imp (Formula.subset ω.weaken.weaken (.bound 1))
    (.imp (sc_index_m (.bound 1) A.weaken.weaken .newest)
      (.existsE (sc_index_m (.bound 2) K.weaken.weaken.weaken .newest)))))
derive_free_closed sc_seq_index_m

theorem sc_seq_index_sat_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x // M.mem x Z}) {n} (ρ : Env (rt_model_l Z hz) n) (ω A K : Term n) :
    Formula.satisfies ρ (sc_seq_index_m ω A K) ↔ ∀ μ e, M.mem μ Z → M.mem e Z →
      M.MemberSubset (ω.eval ρ).val μ → Sc_index_d μ (A.eval ρ).val e → ∃ f, M.mem f Z ∧ Sc_index_d μ (K.eval ρ).val f := by
  have idx {d} (η : Env (rt_model_l Z hz) d) (a b c : Term d) : Formula.satisfies η (sc_index_m a b c) ↔
      Sc_index_d (a.eval η).val (b.eval η).val (c.eval η).val := by
    have tr := (rt_model_delta_l hZ hz (sc_index_delta_l a b c) η).trans (sc_index_sat_l hKP ..)
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using tr
  have sub {d} (η : Env (rt_model_l Z hz) d) (a b : Term d) : Formula.satisfies η (Formula.subset a b) ↔
      M.MemberSubset (a.eval η).val (b.eval η).val := by
    have tr := (rt_model_delta_l hZ hz (.atom _ _ _) η).trans (Formula.satisfies_subset_iff _ a b)
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using tr
  simp only [sc_seq_index_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, sub, idx, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h μ e hμ he hw hi => (h ⟨μ, hμ⟩ ⟨e, he⟩ hw hi).elim fun f hf => ⟨f.val, f.property, hf⟩,
    fun h μ e hw hi => (h μ.val e.val μ.property e.property hw hi).elim fun f hf => ⟨⟨f, hf.1⟩, hf.2⟩⟩

/-- 所有字母表的内部有限列空间及其统一编号。 -/
def sc_seq0_m : Formula 1 1 := .forallE (.existsE (.conj
  (sc_fseq0_m (.bound 2) (.bound 1) .newest)
  (sc_seq_index_m (.bound 2) (.bound 1) .newest)))

theorem sc_seq0_closed_l : sc_seq0_m.FreeClosed := by
  simp -implicitDefEqProofs [sc_seq0_m, sc_fseq0_m, Definitional.Formula.FreeClosed]

def Sc_sequences_d (I : kpair_convention_l.Interpretation M) (w X R : M.Domain) : Prop :=
  Rr_truth_d I X R sc_seq0_m (fun _ : Fin 1 => w)

/-- 所有新字母表的指定有限空间由同一原关系全称句子直接取得。 -/
theorem Sc_sequences_d.space_l (I : kpair_convention_l.Interpretation M) {w X R A : M.Domain}
    (h : Sc_sequences_d I w X R) (hA : M.mem A X) : ∃ K, Sc_fseq_d I w A K X R := by
  obtain ⟨hw, valid⟩ := h
  obtain ⟨K, finite, _⟩ := valid ⟨A, hA⟩
  refine ⟨K.val, Fin.cases K.property (Fin.cases hA (fun _ => hw 0)), ?_⟩
  exact (Formula.closed_env_l (sc_fseq0_m (d := 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (funext (Fin.cases (Subtype.ext rfl)
      (Fin.cases (Subtype.ext rfl) (fun _ => Subtype.ext rfl))))).mp finite

/-- 实际隶属实例用有限函数闭性回收全部背景内部有限图。 -/
theorem sc_sequences_mem_l (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
    {ω c X R : M.Domain} (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (hωX : M.mem ω X)
    (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (un : ∀ a, M.mem a X → ∃ p, M.mem p X ∧ M.IsUnionOf p a) :
    Sc_sequences_d I ω X R ↔
      (∀ A, M.mem A X → ∃ K, M.mem K X ∧ Fseq_space_d (kp_pair_l hKP) ω A K) ∧
      (∀ A K μ e, M.mem A X → M.mem K X → M.mem μ X → M.mem e X →
        Fseq_space_d (kp_pair_l hKP) ω A K → M.MemberSubset ω μ → Sc_index_d μ A e →
          ∃ f, M.mem f X ∧ Sc_index_d μ K f) := by
  have read Z (hZ : M.TransitiveSet Z) (hωZ : M.mem ω Z) (hz : Nonempty {x // M.mem x Z}) :
      Formula.satisfies (⟨fun _ => ⟨ω, hωZ⟩, fun _ => ⟨ω, hωZ⟩⟩ : Env (rt_model_l Z hz) 1) sc_seq0_m ↔
        ∀ A, M.mem A Z → ∃ K, M.mem K Z ∧ (∀ f, M.mem f Z →
          (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f)) ∧ (∀ μ e, M.mem μ Z → M.mem e Z → M.MemberSubset ω μ → Sc_index_d μ A e → ∃ f, M.mem f Z ∧ Sc_index_d μ K f) := by
    have fn (ρ : Env (rt_model_l Z hz) 5) : Formula.satisfies ρ (fn0_m .newest ((.bound 1 : Term 3).weaken.weaken) (.bound 1)) ↔
        Fn0_d (ρ.bound 0).val (ρ.bound 3).val (ρ.bound 1).val :=
      (rt_model_delta_l hZ hz (fn0_delta_l ..) ρ).trans (fn0_sat_l hKP.1 ..)
    simp only [sc_seq0_m, sc_fseq0_m, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      sc_seq_index_sat_l hKP hZ hz, fn]
    constructor
    · intro h A hA
      obtain ⟨K, hK⟩ := h ⟨A, hA⟩
      exact ⟨K.val, K.property, fun f hf => (hK.1 ⟨f, hf⟩).trans
        ⟨fun ⟨n, hn, hf⟩ => ⟨n.val, hn, hf⟩, fun ⟨n, hn, hf⟩ => ⟨⟨n, hZ ω hωZ n hn⟩, hn, hf⟩⟩, hK.2⟩
    · intro h A
      obtain ⟨K, hK, spec, small⟩ := h A.val A.property
      exact ⟨⟨K, hK⟩, fun f => (spec f.val f.property).trans
        ⟨fun ⟨n, hn, hf⟩ => ⟨⟨n, hZ ω hωZ n hn⟩, hn, hf⟩, fun ⟨n, hn, hf⟩ => ⟨n.val, hn, hf⟩⟩, small⟩
  let nz : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let ρ : Env (rt_model_l X nz) 1 := ⟨fun _ => ⟨ω, hωX⟩, fun _ => ⟨ω, hωX⟩⟩
  have raw : Sc_sequences_d I ω X R ↔ Formula.satisfies ρ sc_seq0_m :=
    ⟨fun ⟨_, valid⟩ => (smem_formula_l I hm nz sc_seq0_m ρ).mpr valid,
      fun valid => ⟨fun _ => hωX, (smem_formula_l I hm nz sc_seq0_m ρ).mp valid⟩⟩
  rw [raw, read X hX hωX nz]
  constructor
  · intro target
    have full A K (hA : M.mem A X) (hK : M.mem K X)
        (spec : ∀ f, M.mem f X → (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f)) :
        Fseq_space_d (kp_pair_l hKP) ω A K := by
      intro f
      constructor
      · intro hf
        obtain ⟨n, hn, hf⟩ := (spec f (hX K hK f hf)).mp hf
        exact ⟨n, hn, fn0_function_l hKP hf⟩
      · rintro ⟨n, hn, hf⟩
        have fn := fn0_of_function_l hKP hf
        exact (spec f (sc_finite_function_l hKP hω hX pair un hωX (hX A hA) hn fn)).mpr ⟨n, hn, fn⟩
    refine ⟨fun A hA => ?_, fun A K μ e hA _ hμ he hK hw idx => ?_⟩
    · obtain ⟨K, hk, spec, _⟩ := target A hA
      exact ⟨K, hk, full A K hA hk spec⟩
    · obtain ⟨L, hl, spec, bound⟩ := target A hA
      exact hKP.1.eq_of_same_members L K (fun f => (full A L hA hl spec f).trans (hK f).symm) ▸ bound μ e hμ he hw idx
  · rintro ⟨space, index⟩ A hA
    obtain ⟨K, hK, spec⟩ := space A hA
    exact ⟨K, hK, fun f _ => (spec f).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l hKP, fn0_function_l hKP⟩), fun μ e hμ he => index A K μ e hA hK hμ he spec⟩

/-- 背景程序的 ω 与公式参数中的内部自然数对象分别保留。 -/
theorem sc_sequences_iff_l (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF)
    {ω w w' c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (image : M.PairMember I w w' q) : Sc_sequences_d I w X R ↔ Sc_sequences_d I w' Y S := by
  have hx := hq.1.1.input_mem_of_pairMember image
  have hy := hq.1.1.output_mem_of_pairMember image
  let ρ : Env (smdl_structure_l I (R := R) hm.2.1) 1 := ⟨fun _ => ⟨w, hx⟩, fun _ => ⟨w, hx⟩⟩
  let η : Env (smdl_structure_l I (R := S) hn.2.1) 1 := ⟨fun _ => ⟨w', hy⟩, fun _ => ⟨w', hy⟩⟩
  have transfer := smap_source_l I hZF hω hm hn hq sc_seq0_m sc_seq0_closed_l ρ η (fun _ => image)
  exact ⟨fun h => ⟨fun _ => hy, transfer.mp h.2⟩, fun h => ⟨fun _ => hx, transfer.mpr h.2⟩⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定有限列空间的实际像仍是完整有限列空间。 -/
theorem Smap_d.sequences_l {ω c d X R Y S j A A' K K' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (theory : Sc_theory_d I ω Y S) (hωX : M.mem ω X)
    (hA : Rd_entry_d A A' j) (hK : Rd_entry_d K K' j) (space : Fseq_space_d I ω A K) : Fseq_space_d I ω A' K' := by
  have hωj := hj.omega_l I hZF hω hX hY hm hn hωX
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1)))
  have tr := hj.forall_delta_l hZF hω hX hY hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.iff (.mem ..) (.existsMem _ (fn0_delta_l ..)))
    ⟨Fin.cases K (Fin.cases A (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases K' (Fin.cases A' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hK (Fin.cases hA (fun _ => hωj)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1] at tr
  have read := tr.mp (fun f _ => (space f).trans (exists_congr fun n => and_congr_right fun _ =>
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩))
  intro f
  refine ⟨fun hf => ?_, fun ⟨n, hnω, fn⟩ => ?_⟩
  · obtain ⟨n, hnω, fn⟩ := (read f (hY K' (hj.1.1.output_mem_of_pairMember hK) f hf)).mp hf
    exact ⟨n, hnω, fn0_function_l (ZF.modelsKP hZF) fn⟩
  · have fn := fn0_of_function_l (ZF.modelsKP hZF) fn
    exact (read f (sc_finite_function_l (ZF.modelsKP hZF) hω hY (theory.algebra_l _ (ZF.modelsKP hZF) hY hn).pair (theory.algebra_l _ (ZF.modelsKP hZF) hY hn).union (hj.1.1.output_mem_of_pairMember hωj)
      (hY A' (hj.1.1.output_mem_of_pairMember hA)) hnω fn)).mpr ⟨n, hnω, fn⟩

theorem Sc_sequences_d.small_l {ω c X R A K : M.Domain} (h : Sc_sequences_d I ω X R)
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hωX : M.mem ω X) (hA : M.mem A X) (hK : M.mem K X) (seq : Fseq_space_d I ω A K)
    (small : Sc_small_d X A) : Sc_small_d X K := by
  obtain ⟨μ, e, hμ, he, hw, idx⟩ := sc_infinite_index_l hZF hω hX hm theory hωX hA small
  have algebra := theory.algebra_l I (ZF.modelsKP hZF) hX hm
  have read := (sc_sequences_mem_l I (ZF.modelsKP hZF) hω hX hm hωX algebra.pair algebra.union).mp h
  obtain ⟨f, hf, hi⟩ := read.2 A K μ e hA hK hμ he seq hw idx
  exact ⟨μ, f, hμ, hf, hi⟩

theorem sc_h_sequences_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    {c R : M.Domain} (model : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c H R) :
    Sc_sequences_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H R := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kp_pair_l (ZF.modelsKP hZF)
  have algebra := sc_h_algebra_l hZFC hω hχ hωχ hH
  apply (sc_sequences_mem_l J (ZF.modelsKP hZF) hω (ZF.h_transitive_l J hZF hH) model
    (ZF.h_ordinal_l J hZF hχ.isLimitOrdinal hH hωχ) algebra.pair algebra.union).mpr
  refine ⟨fun _ => ZFC.h_fseq_l hZFC hω hχ hωχ hH, fun A K μ e _ hK hμ _ seq hw idx => ?_⟩
  obtain ⟨f, hf⟩ := ZF.fseq_ordinal_bound_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω idx.ordinal hw (idx.bound_l (ZF.modelsKP hZF)) seq
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hH hK
    (hf.1.mono_target_l (kp_pair_l (ZF.modelsKP hZF)) (ZF.h_transitive_l (kp_pair_l (ZF.modelsKP hZF)) hZF hH μ hμ)), Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal hf⟩

theorem sc_v_sequences_l {ω δ V : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hωδ : M.mem ω δ) (hV : V_d I δ V) {c R : M.Domain} (model : Smem_d I c V R) : Sc_sequences_d I ω V R := by
  have hωV := ZF.v_ordinal_mem_l I hZF hV hωδ
  have un a (ha : M.mem a V) : ∃ p, M.mem p V ∧ M.IsUnionOf p a := by
    obtain ⟨β, Y, hβ, hY, hAY⟩ := (ZF.v_unfold_l I hZF hV a).mp ha
    obtain ⟨p, hp⟩ := KP.exists_union (ZF.modelsKP hZF) a
    exact ⟨p, v_subset_mem_l I hV (ZF.v_mem_l I hZF hY hV hβ) (fun t ht =>
      ((hp t).mp ht).elim fun b hb => v_transitive_l I hY b (hAY b hb.1) t hb.2), hp⟩
  apply (sc_sequences_mem_l I (ZF.modelsKP hZF) hω (v_transitive_l I hV) model hωV
    (sc_v_pair_l (ZF.modelsKP hZF) hδ hV) un).mpr
  refine ⟨fun A hA => ?_, fun A K μ e _ hK hμ _ seq hw idx => ?_⟩
  · obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω A
    exact ⟨K, ZF.v_fseq_mem_l I hZF hV hδ hω hωV hA hK, hK⟩
  · obtain ⟨q, hq⟩ := ZF.fseq_ordinal_bound_l I hZF hω idx.ordinal hw (idx.bound_l (ZF.modelsKP hZF)) seq
    obtain ⟨Y, hY, hKY, hμY⟩ := v_joint_bound_l I hV hK hμ
    have hqV := v_relation_mem_l I hV hδ hY (fun p hp =>
      (fn0_of_function_l (ZF.modelsKP hZF) hq.1).1 p hp |>.elim fun a ha => ha.2.elim fun b hb =>
        ⟨a, hKY a ha.1, b, hμY b hb.1, hb.2⟩)
    exact ⟨q, hqV, Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal hq⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源闭包在背景模型中的单一公式

量化背景模型中的全部内部程序码、赋值和源内集合参数。具名量词直接编译到已有公式，
因此有限历史可用背景的分离及依赖选择处理，也覆盖非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 相对化只需结构内部的传递性；背景结构本身可以是未坍塌的商关系。 -/
theorem sc_relative_sat_l {C : M.Domain} (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) {n d} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l C nc) n) (η : Env M d) (T : Term d) (a : Fin n → Term d)
    (hT : T.eval η = C) (params : ∀ i, (a i).eval η = (ρ.bound i).val) :
    Formula.satisfies η (lr_rel_m φ T a) ↔ Formula.satisfies ρ φ := by
  have term {n d} (ρ : Env (rt_model_l C nc) n) (η : Env M d) (a : Fin n → Term d)
      (ha : ∀ i, (a i).eval η = (ρ.bound i).val) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind a).eval η = (t.eval ρ).val := by
    cases t with
    | free _ => cases ht
    | bound i => exact ha i
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at closed
  case falsum | truth => rfl
  case mem s t =>
    simp only [lr_rel_m, Formula.satisfies_mem_iff, term ρ η a params s closed.1,
      term ρ η a params t closed.2]; rfl
  case atom r hr ts =>
    have eq := rt_model_delta_l trans nc (φ := .atom r hr ts) (.atom ..) ρ
    cases r <;>
      simpa only [lr_rel_m, Formula.satisfies_atom_extensionalEq_iff,
        Formula.satisfies_atom_subset_iff, Definitional.TermVector.get_bind,
        term ρ η a params (ts 0) (closed 0), term ρ η a params (ts 1) (closed 1),
        @eval_image_env_l (rt_model_l C nc) M Subtype.val] using eq.symm
  case neg φ ih => exact not_congr (ih closed ρ η T a hT params)
  case conj φ ψ ih jh => exact and_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case disj φ ψ ih jh => exact or_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case imp φ ψ ih jh => exact imp_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case iff φ ψ ih jh => exact iff_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case existsE φ ih | forallE φ ih =>
    have next (x : (rt_model_l C nc).Domain) := ih closed (ρ.push x) (η.push x.val) T.weaken
      (Fin.cases .newest (fun i => (a i).weaken)) (by simpa using hT)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken η x.val (a i)).trans (params i)))
    first
    | rw [lr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (next ⟨x, hx⟩).mp h⟩,
        fun ⟨x, h⟩ => ⟨x.val, x.property, (next x).mpr h⟩⟩
    | rw [lr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, hT]
      exact ⟨fun h x => (next x).mp (h x.val x.property), fun h x hx => (next ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

def sc_small0_m {d} (X A : Term d) : Formula 1 d := set[d] ⟪
  ∃ μ ∈ ⌜X⌝ₛ, ∃ f ∈ ⌜X⌝ₛ, ⌜sc_index_m⌝ₚ(μ, ⌜A⌝ₛ, f)⟫
derive_free_closed sc_small0_m

theorem sc_small0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X A : Term d) :
    Formula.satisfies ρ (sc_small0_m X A) ↔ Sc_small_d (X.eval ρ) (A.eval ρ) := by
  simp only [sc_small0_m, Formula.satisfies_existsMem_iff, sc_index_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨μ, hμ, f, hf, idx⟩ => ⟨μ, f, hμ, hf, idx⟩,
    fun ⟨μ, f, hμ, hf, idx⟩ => ⟨μ, hμ, f, hf, idx⟩⟩

def sc_separation_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i f D,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → f ∈ E → D ∈ ⌜X⌝ₛ → ∃ A ∈ ⌜X⌝ₛ,
      ∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x,A,⌜R⌝ₛ) ↔
        ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x,D,⌜R⌝ₛ) ∧ (∃ g,
        ⌜senv_update_m (𝒞 := kpair_convention_l)⌝ₚ(f, i, x, g) ∧
        ⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, g))⟫
derive_free_closed sc_separation_m

theorem sc_separation_sat_l (hE : Extensional M) (I : kpair_convention_l.Interpretation M)
    {d} (ρ : Env M d) (ω X R : Term d) : Formula.satisfies ρ (sc_separation_m ω X R) ↔
      ∀ E F n r i f D, M.IsFunctionSpace I E (ω.eval ρ) (X.eval ρ) → Sfm_d I (ω.eval ρ) n F →
        M.mem r n → M.mem i (ω.eval ρ) → M.mem f E → M.mem D (X.eval ρ) →
          ∃ A, M.mem A (X.eval ρ) ∧ Sr_sep_d I (X.eval ρ) (R.eval ρ) E F n r i f D A := by
  simp only [sc_separation_m, Sr_sep_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isFunctionSpace_iff I hE,
    sfm_sat_l I hE, senv_update_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def sc_sequences0_m {d} (w X R : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) sc_seq0_m X R (fun _ : Fin 1 => w)

@[simp] theorem sc_sequences0_closed_l {d} (w X R : Term d)
    (hw : w.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = []) :
    (sc_sequences0_m w X R).FreeClosed :=
  rr_truth_closed_l sc_seq0_m sc_seq0_closed_l X R (fun _ : Fin 1 => w) hX hR (fun _ => hw)

theorem sc_sequences0_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d) (w X R : Term d) :
    Formula.satisfies ρ (sc_sequences0_m w X R) ↔ Sc_sequences_d I (w.eval ρ) (X.eval ρ) (R.eval ρ) :=
  rr_truth_sat_l I ρ sc_seq0_m sc_seq0_closed_l X R (fun _ : Fin 1 => w)

end YesMetaZFC.SetTheory.Internal
