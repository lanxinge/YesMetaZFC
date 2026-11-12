import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.ProjectEmbedding
import YesMetaZFC.SetTheory.InnerModel.Separation.Formula
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Closure

/-! # 带集合谓词的内部初等嵌入

在无自隶属的集合载体上，用 R(x,y) ↔ x∈y ∨ (x=y ∧ x∈A)
编码 (X,∈,A)。对角线恢复 A，非对角线恢复 ∈；统一满足关系仍使用原内部公式码。
嵌入、赋值及其复合均为模型内集合，初等性量化包括非标准码在内的全部内部公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Spred_d (c X A R : M.Domain) : Prop := Smdl_d I c X R ∧ M.MemberSubset A X ∧
  ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ (M.mem x y ∨ x = y ∧ M.mem x A)

def spred_m {n} (c X A R : Term n) : Formula 1 n :=
  .conj (smdl_m (𝒞 := 𝒞) c X R) (.conj (Formula.subset A X)
    (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken)
        (.disj (.mem (.bound 1) .newest) (.conj (Formula.extensionalEq (.bound 1) .newest)
          (.mem (.bound 1) A.weaken.weaken)))))))))
derive_free_closed spred_m

theorem spred_sat_l (hE : Extensional M) {n} (ρ : Env M n) (c X A R : Term n) :
    Formula.satisfies ρ (spred_m (𝒞 := 𝒞) c X A R) ↔ Spred_d I (c.eval ρ) (X.eval ρ) (A.eval ρ) (R.eval ρ) := by
  simp only [spred_m, Spred_d, Formula.satisfies_conj_iff, smdl_sat_l I, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]
  rfl

/-- 每个实际集合谓词都生成结构码；不要求它可由载体内部公式定义。 -/
theorem spred_exists_l (hZF : M.Models ZF) {X A} (hX : ∃ x, M.mem x X) (hA : M.MemberSubset A X) :
    ∃ c R, Spred_d I c X A R := by
  let φ : BinarySchema 1 := {
    body := .disj (.mem (.bound 1) .newest)
      (.conj (Formula.extensionalEq (.bound 1) .newest) (.mem (.bound 1) (.bound 2))) }
  obtain ⟨c, R, hc, hr⟩ := smdl_exists_l I hZF φ ⟨fun _ => A, fun _ => A⟩ hX
  refine ⟨c, R, hc, hA, fun x y => (hr x y).trans (and_congr_right fun _ => and_congr_right fun _ => ?_)⟩
  simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
  rfl

/-- 编码的两个原子可精确还原，因此没有改变 (∈,A) 的数学内容。 -/
theorem spred_read_l (hKP : M.Models KP) {c X A R} (h : Spred_d I c X A R) (x y : M.Domain) :
    (M.PairMember I x x R ↔ M.mem x A) ∧
      (M.PairMember I x y R ∧ x ≠ y ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y) := by
  constructor
  · rw [h.2.2 x x]
    exact ⟨fun hx => hx.2.2.elim (fun h => (KP.mem_irrefl_d hKP x h).elim) And.right,
      fun hx => ⟨h.2.1 x hx, h.2.1 x hx, Or.inr ⟨rfl, hx⟩⟩⟩
  · rw [h.2.2 x y]
    exact ⟨fun ⟨hx, hn⟩ => ⟨hx.1, hx.2.1, hx.2.2.elim id (fun h => (hn h.1).elim)⟩,
      fun ⟨hx, hy, hm⟩ => ⟨⟨hx, hy, Or.inl hm⟩, fun he => KP.mem_irrefl_d hKP y (he ▸ hm)⟩⟩

def Smap_assign_d (ω j f g : M.Domain) : Prop := ∀ n, M.mem n ω → ∀ x y,
  M.PairMember I n x f → M.PairMember I x y j → M.PairMember I n y g

def smap_assign_m {d} (ω j f g : Term d) : Formula 1 d := Formula.forallMem ω
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) f.weaken.weaken.weaken)
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest j.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 2) .newest g.weaken.weaken.weaken)))))
derive_free_closed smap_assign_m

theorem smap_assign_sat_l {d} (ρ : Env M d) (ω j f g : Term d) :
    Formula.satisfies ρ (smap_assign_m (𝒞 := 𝒞) ω j f g) ↔
      Smap_assign_d I (ω.eval ρ) (j.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [smap_assign_m, Smap_assign_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem smap_assign_exists_l (hZF : M.Models ZF) {ω X Y j f}
    (hj : M.IsSetFunctionFromTo I j X Y) (hf : M.IsSetFunctionFromTo I f ω X) :
    ∃ g, M.IsSetFunctionFromTo I g ω Y ∧ Smap_assign_d I ω j f g := by
  obtain ⟨g, hg, he⟩ := ZF.exists_compositionFunction hZF I hf hj
  exact ⟨g, hg, fun n hn x y hx hy => (he n y).mpr ⟨hn, x, hx, hy⟩⟩

def Smap_d (ω c d X Y j : M.Domain) : Prop := M.IsSetInjectionFromTo I j X Y ∧
  ∃ C, Scode_d I ω C ∧ ∀ a f g, M.mem a C → M.IsSetFunctionFromTo I f ω X →
    M.IsSetFunctionFromTo I g ω Y → Smap_assign_d I ω j f g →
      (Satisfies_d I ω c a f ↔ Satisfies_d I ω d a g)

def smap_m {n} (ω c d X Y j : Term n) : Formula 1 n :=
  .conj (Formula.isInjectionFromTo 𝒞 j X Y) (.existsE (.conj (scode_m (𝒞 := 𝒞) ω.weaken .newest)
    (Formula.forallMem .newest (.forallE (.forallE (.imp
      (Formula.isFunctionFromTo 𝒞 (.bound 1) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken)
      (.imp (Formula.isFunctionFromTo 𝒞 .newest ω.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken)
        (.imp (smap_assign_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken j.weaken.weaken.weaken.weaken (.bound 1) .newest)
          (.iff (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
            (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken d.weaken.weaken.weaken.weaken (.bound 2) .newest))))))))))
derive_free_closed smap_m

theorem smap_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c d X Y j : Term n) :
    Formula.satisfies ρ (smap_m (𝒞 := 𝒞) ω c d X Y j) ↔
      Smap_d I (ω.eval ρ) (c.eval ρ) (d.eval ρ) (X.eval ρ) (Y.eval ρ) (j.eval ρ) := by
  simp only [smap_m, Smap_d, Formula.satisfies_conj_iff, Formula.satisfies_isInjectionFromTo_iff I hE,
    Formula.satisfies_exists_iff, scode_sat_l I hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    smap_assign_sat_l I, Formula.satisfies_iff_iff, satisfies_sat_l I hE, Definitional.Term.eval_weaken]
  exact and_congr Iff.rfl (exists_congr fun C => and_congr Iff.rfl
    ⟨fun h a f g ha => h a ha f g, fun h a ha f g => h a f g ha⟩)

/-- 完整初等证书直接作用于任意合法内部程序行，无需调用者另打包公式码。 -/
theorem Smap_d.ssat_l (hE : Extensional M) {ω c d X R Y S E K j n F r f g}
    (h : Smap_d I ω c d X Y j) (hX : Smdl_d I c X R) (hY : Smdl_d I d Y S)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hA : M.IsFunctionSpace I E ω X)
    (hB : M.IsFunctionSpace I K ω Y) (hf : M.mem f E) (hg : M.mem g K) (hfg : Smap_assign_d I ω j f g) :
    Ssat_d I X R E F n r f ↔ Ssat_d I Y S K F n r g := by
  obtain ⟨a, ha⟩ := I.total F r
  have hc : Sformula_d I ω a n F r := ⟨ha, hF, hr⟩
  obtain ⟨C, hC, hh⟩ := h.2
  exact (satisfies_decode_l I hE hX hc hA).symm.trans
    ((hh a f g ((hC a).mpr ⟨n, F, r, hc⟩) ((hA f).mp hf) ((hB g).mp hg) hfg).trans
      (satisfies_decode_l I hE hY hc hB))

def Spred_emb_d (ω X A Y B j : M.Domain) : Prop := ∃ c R d S,
  Spred_d I c X A R ∧ Spred_d I d Y B S ∧ Smap_d I ω c d X Y j

def spred_emb_m {n} (ω X A Y B j : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.conj
    (spred_m (𝒞 := 𝒞) (.bound 3) X.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 2)) (.conj
    (spred_m (𝒞 := 𝒞) (.bound 1) Y.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken .newest)
    (smap_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1)
      X.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken j.weaken.weaken.weaken.weaken))))))
derive_free_closed spred_emb_m

theorem spred_emb_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X A Y B j : Term n) :
    Formula.satisfies ρ (spred_emb_m (𝒞 := 𝒞) ω X A Y B j) ↔
      Spred_emb_d I (ω.eval ρ) (X.eval ρ) (A.eval ρ) (Y.eval ρ) (B.eval ρ) (j.eval ρ) := by
  simp only [spred_emb_m, Spred_emb_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    spred_sat_l I hE, smap_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 实际恒等图及其全内部初等性，同时保留逐点图方程。 -/
theorem smap_identity_l (hZF : M.Models ZF) {ω X c} (hω : M.IsOmega ω) :
    ∃ j, Smap_d I ω c c X X j ∧ ∀ x y, M.PairMember I x y j ↔ M.mem x X ∧ x = y := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => X⟩
  have hd x y := Formula.denote_identityValue_iff hZF.1 ρ x y
  obtain ⟨j, hj, hj'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I BinarySchema.identityValue ρ
    (source := X) (target := X) (fun x _ => ⟨x, (hd x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((hd x y).mp hy).symm.trans ((hd x z).mp hz))
    (fun x y hx hy => (hd x y).mp hy ▸ hx)
  have he x y : M.PairMember I x y j ↔ M.mem x X ∧ x = y :=
    (hj' x y).trans (and_congr_right fun _ => hd x y)
  have hi : M.IsSetInjectionFromTo I j X X := ⟨hj,
    fun x y z hx hy => ((he x z).mp hx).2.trans ((he y z).mp hy).2.symm⟩
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  refine ⟨j, ⟨hi, C, hC, fun a f g _ hf hg hh => ?_⟩, he⟩
  have eq : f = g := hf.1.1.eq_of_pairMember_iff hZF.1 hg.1.1 (fun n x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · exact eq ▸ Iff.rfl
  · exact hh n (hf.input_mem_of_pairMember hx) x x hx ((he x x).mpr ⟨hf.output_mem_of_pairMember hx, rfl⟩)
  · obtain ⟨y, hy, hny⟩ := hf.2.2 n (hg.input_mem_of_pairMember hx)
    have hng := hh n (hg.input_mem_of_pairMember hx) y y hny ((he y y).mpr ⟨hy, rfl⟩)
    exact hg.1.2 n y x hng hx ▸ hny

/-- 恒等图给出每个实际带谓词集合结构的初等嵌入实例。 -/
theorem spred_identity_l (hZF : M.Models ZF) {ω X A} (hω : M.IsOmega ω)
    (hX : ∃ x, M.mem x X) (hA : M.MemberSubset A X) : ∃ j, Spred_emb_d I ω X A X A j := by
  obtain ⟨c, R, hc⟩ := spred_exists_l I hZF hX hA
  obtain ⟨j, hj, _⟩ := smap_identity_l I hZF (X := X) (c := c) hω
  exact ⟨j, c, R, c, R, hc, hc, hj⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部嵌入对原公式的实际作用

先给原公式构造内部码与有限参数赋值，再沿实际嵌入复合赋值图。
两边读取同一内部码，故全内部初等性直接给出逐公式保持，无额外语义合同。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smap_source_l (hZF : M.Models ZF) {ω c d X Y R S j} (hω : M.IsOmega ω)
    (hX : Smdl_d I c X R) (hY : Smdl_d I d Y S) (hj : Smap_d I ω c d X Y j) {n}
    (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) hX.2.1) n)
    (η : Env (smdl_structure_l I (R := S) hY.2.1) n)
    (hp : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val j) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨a, l, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω Y
  have hi : Function.Injective v := fun i r h => Fin.ext
    (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv r))
  obtain ⟨f, hf, hρ⟩ := senv_params_l I hZF hE hX.2.1 v (fun i => (ρ.bound i).val)
    hi (fun i => num_mem_l hZF.1 hω (hv i)) (fun i => (ρ.bound i).property)
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hj.1.1 ((hE f).mp hf)
  have hη i := hfg (v i) (num_mem_l hZF.1 hω (hv i)) (ρ.bound i).val (η.bound i).val (hρ i) (hp i)
  obtain ⟨C, hC, ht⟩ := hj.2
  exact ((satisfies_decode_l I hZF.1 hX ha hE).trans (hc X R hX.2.1 E hE f hf ρ hρ)).symm.trans
    ((ht a f g ((hC a).mpr ⟨l, F, k, ha⟩) ((hE f).mp hf) hg hfg).trans
      ((satisfies_decode_l I hZF.1 hY ha hD).trans (hc Y S hY.2.1 D hD g ((hD g).mpr hg) η hη)))

theorem Smap_d.relation_l (hZF : M.Models ZF) {ω c d X R Y S j x y x' y' : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hx : M.PairMember I x x' j) (hy : M.PairMember I y y' j) :
    M.PairMember I x y R ↔ M.PairMember I x' y' S := by
  exact smap_source_l I hZF hω hm hn hj (n := 2)
    (.mem (.bound (Fin.succ 0)) .newest) ⟨rfl, rfl⟩
    ⟨Fin.cases ⟨y, hj.1.1.input_mem_of_pairMember hy⟩ (fun _ => ⟨x, hj.1.1.input_mem_of_pairMember hx⟩),
      fun _ => ⟨x, hj.1.1.input_mem_of_pairMember hx⟩⟩
    ⟨Fin.cases ⟨y', hj.1.1.output_mem_of_pairMember hy⟩ (fun _ => ⟨x', hj.1.1.output_mem_of_pairMember hx⟩),
      fun _ => ⟨x', hj.1.1.output_mem_of_pairMember hx⟩⟩ (Fin.cases hy (fun _ => hx))

/-- 隶属结构之间的完整初等图反映实际隶属关系。 -/
theorem Smap_d.member_l (hZF : M.Models ZF) {ω c d X R Y S j x y x' y' : M.Domain}
    (hω : M.IsOmega ω) (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hx : M.PairMember I x x' j) (hy : M.PairMember I y y' j) : M.mem x y ↔ M.mem x' y' := by
  have tr := hj.relation_l I hZF hω hm.1 hn.1 hx hy
  exact ⟨fun h => ((hn.2 x' y').mp (tr.mp ((hm.2 x y).mpr
    ⟨hj.1.1.input_mem_of_pairMember hx, hj.1.1.input_mem_of_pairMember hy, h⟩))).2.2,
    fun h => ((hm.2 x y).mp (tr.mpr ((hn.2 x' y').mpr
      ⟨hj.1.1.output_mem_of_pairMember hx, hj.1.1.output_mem_of_pairMember hy, h⟩))).2.2⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原内部初等图的实际模型映射

从已实现的全内部初等图读取逐点映射，并由原编译器得到所有 Project
公式的初等性。选择只位于存在命题中，不导出不可计算数据实例。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smap_d.project_l (hZF : M.Models ZF) {ω c d X Y R S j : M.Domain} (hw : M.IsOmega ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j) :
    ∃ f : (smdl_structure_l I (R := R) mx.2.1).Domain → (smdl_structure_l I (R := S) my.2.1).Domain,
      Pe_d f ∧ ∀ x, M.PairMember I x.val (f x).val j := by
  have values (x : (smdl_structure_l I (R := R) mx.2.1).Domain) :
      ∃ y : (smdl_structure_l I (R := S) my.2.1).Domain, M.PairMember I x.val y.val j := by
    obtain ⟨y, hy, xy⟩ := map.1.1.2.2 x.val x.property
    exact ⟨⟨y, hy⟩, xy⟩
  obtain ⟨f, values⟩ := Classical.axiomOfChoice values
  exact ⟨f, fun φ hc ρ => smap_source_l I hZF hw mx my map φ hc ρ (image_env_l f ρ)
    (fun i => values (ρ.bound i)), values⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 从谓词结构嵌入读取原集合论公式

谓词图的对角线只记录 A。Foundation 保证 x∈y 恰好是 R(x,y)∧¬R(y,x)，
故先展开生产原子，再作统一关系替换，就能完整恢复原隶属语言。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem spred_mem_l (hKP : M.Models KP) {c X A R} (h : Spred_d I c X A R)
    {x y} (hx : M.mem x X) (hy : M.mem y X) :
    M.PairMember I x y R ∧ ¬ M.PairMember I y x R ↔ M.mem x y := by
  have asymm {x y} (hxy : M.mem x y) : ¬ M.mem y x := by
    intro hyx
    obtain ⟨P, hp⟩ := KP.exists_pair hKP x y
    obtain ⟨z, hz, hm⟩ := KP.mem_minimal_exists_d hKP ⟨x, (hp x).mpr (Or.inl rfl)⟩
    rcases (hp z).mp hz with rfl | rfl
    · exact hm y ((hp y).mpr (Or.inr rfl)) hyx
    · exact hm x ((hp x).mpr (Or.inl rfl)) hxy
  constructor
  · rintro ⟨hxy, hn⟩
    rcases ((h.2.2 x y).mp hxy).2.2 with hm | ⟨rfl, _⟩
    · exact hm
    · exact (hn hxy).elim
  · intro hxy
    refine ⟨(h.2.2 x y).mpr ⟨hx, hy, Or.inl hxy⟩, fun hyx => ?_⟩
    rcases ((h.2.2 y x).mp hyx).2.2 with hm | ⟨rfl, _⟩
    · exact asymm hxy hm
    · exact KP.mem_irrefl_d hKP _ hxy

def spred_core_l : {n : Nat} → Formula 0 n → Formula 1 n
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem s t => .conj (.mem s t) (.neg (.mem t s))
  | _, .atom _ h _ => by have h : (0 : Nat) < 0 := h; omega
  | _, .neg φ => .neg (spred_core_l φ)
  | _, .conj φ ψ => .conj (spred_core_l φ) (spred_core_l ψ)
  | _, .disj φ ψ => .disj (spred_core_l φ) (spred_core_l ψ)
  | _, .imp φ ψ => .imp (spred_core_l φ) (spred_core_l ψ)
  | _, .iff φ ψ => .iff (spred_core_l φ) (spred_core_l ψ)
  | _, .forallE φ => .forallE (spred_core_l φ)
  | _, .existsE φ => .existsE (spred_core_l φ)

theorem spred_core_closed_l {n} (φ : Formula 0 n) (hφ : φ.FreeClosed) : (spred_core_l φ).FreeClosed := by
  induction φ <;> simp only [spred_core_l, Definitional.Formula.FreeClosed] at hφ ⊢
  case atom _ h _ => have h : (0 : Nat) < 0 := h; omega
  case mem s t => exact ⟨hφ, hφ.2, hφ.1⟩
  case neg φ ih | forallE φ ih | existsE φ ih => exact ih hφ
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh => exact ⟨ih hφ.1, jh hφ.2⟩

theorem spred_core_sat_l (hKP : M.Models KP) {c X A R} (h : Spred_d I c X A R)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {n} (φ : Formula 0 n)
    (ρ : Env (rt_model_l X hn) n) :
    Formula.satisfies (⟨ρ.bound, ρ.free⟩ : Env (smdl_structure_l I (R := R) h.1.2.1) n) (spred_core_l φ) ↔
      Definitional.Semantics.satisfies Semantics.interpretation ρ φ := by
  induction φ <;> simp only [spred_core_l, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Definitional.Semantics.satisfies]
  case atom _ ht _ => have ht : (0 : Nat) < 0 := ht; omega
  case mem s t => exact spred_mem_l I hKP h (s.eval ρ).property (t.eval ρ).property
  case neg φ ih => exact not_congr (ih ρ)
  case conj φ ψ ih jh => exact and_congr (ih ρ) (jh ρ)
  case disj φ ψ ih jh => exact or_congr (ih ρ) (jh ρ)
  case imp φ ψ ih jh => exact imp_congr (ih ρ) (jh ρ)
  case iff φ ψ ih jh => exact iff_congr (ih ρ) (jh ρ)
  case forallE φ ih => exact forall_congr' (fun x => ih (ρ.push x))
  case existsE φ ih => exact exists_congr (fun x => ih (ρ.push x))

/-- 带谓词初等嵌入对整个原隶属语言初等，不要求两个载体先满足 ZF。 -/
theorem spred_source_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hn : Nonempty {x : M.Domain // M.mem x X})
    (hm : Nonempty {x : M.Domain // M.mem x Y}) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (rt_model_l X hn) n) (η : Env (rt_model_l Y hm) n)
    (hp : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val j) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  let ψ := spred_core_l (source_core_l φ)
  have tr (Z P Q c) (hz : Spred_d I c Z P Q) (hz' : Nonempty {x // M.mem x Z})
      (ρ : Env (rt_model_l Z hz') n) :=
    (spred_core_sat_l I (ZF.modelsKP hZF) hz hz' (source_core_l φ) ρ).trans (source_core_sat_l φ ρ)
  exact (tr X A R c hx hn ρ).symm.trans ((smap_source_l I hZF hω hx.1 hy.1 hj ψ
    (spred_core_closed_l _ (source_core_closed_l φ hφ)) ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ hp).trans
      (tr Y B S d hy hm η))

/-- 传递载体之间，原 Δ₀ 公式的保持可直接在背景模型中调用。 -/
theorem spred_delta_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    {n} (φ : Formula 1 n) (hf : φ.FreeClosed) (hd : φ.IsDelta0)
    (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) j) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  have hρ i := hj.1.1.input_mem_of_pairMember (hp i)
  have hη i := hj.1.1.output_mem_of_pairMember (hp i)
  obtain ⟨x, hxX⟩ := hx.1.2.1
  obtain ⟨y, hyY⟩ := hy.1.2.1
  let hn : Nonempty {x // M.mem x X} := ⟨⟨x, hxX⟩⟩
  let hm : Nonempty {x // M.mem x Y} := ⟨⟨y, hyY⟩⟩
  let ρ' : Env (rt_model_l X hn) n := ⟨fun i => ⟨ρ.bound i, hρ i⟩, fun _ => ⟨x, hxX⟩⟩
  let η' : Env (rt_model_l Y hm) n := ⟨fun i => ⟨η.bound i, hη i⟩, fun _ => ⟨y, hyY⟩⟩
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hx, hy, hj⟩ hn hm φ hf ρ' η' hp
  have hr : Formula.satisfies ρ' φ ↔ Formula.satisfies ρ φ :=
    (rt_model_delta_l hX hn hd ρ').trans (Formula.closed_env_l φ hf rfl)
  have hs : Formula.satisfies η' φ ↔ Formula.satisfies η φ :=
    (rt_model_delta_l hY hm hd η').trans (Formula.closed_env_l φ hf rfl)
  exact hr.symm.trans (tr.trans hs)

/-- 全称量词覆盖目标载体中的全部对象，包括不在 j 的像中的有限支撑。 -/
theorem spred_forall_delta_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    {n} (φ : Formula 1 (n + 1)) (hf : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) j) :
    (∀ x, M.mem x X → Formula.satisfies (ρ.push x) φ) ↔
      ∀ y, M.mem y Y → Formula.satisfies (η.push y) φ := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  obtain ⟨x, hxX⟩ := hx.1.2.1
  obtain ⟨y, hyY⟩ := hy.1.2.1
  let hn : Nonempty {x // M.mem x X} := ⟨⟨x, hxX⟩⟩
  let hm : Nonempty {x // M.mem x Y} := ⟨⟨y, hyY⟩⟩
  let ρ' : Env (rt_model_l X hn) n :=
    ⟨fun i => ⟨ρ.bound i, hj.1.1.input_mem_of_pairMember (hp i)⟩, fun _ => ⟨x, hxX⟩⟩
  let η' : Env (rt_model_l Y hm) n :=
    ⟨fun i => ⟨η.bound i, hj.1.1.output_mem_of_pairMember (hp i)⟩, fun _ => ⟨y, hyY⟩⟩
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hx, hy, hj⟩ hn hm (.forallE φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hf) ρ' η' hp
  have hr (a : (rt_model_l X hn).Domain) : Formula.satisfies (ρ'.push a) φ ↔ Formula.satisfies (ρ.push a.val) φ :=
    (rt_model_delta_l hX hn hd _).trans (Formula.closed_env_l φ hf (by funext i; exact Fin.cases rfl (fun _ => rfl) i))
  have hs (b : (rt_model_l Y hm).Domain) : Formula.satisfies (η'.push b) φ ↔ Formula.satisfies (η.push b.val) φ :=
    (rt_model_delta_l hY hm hd _).trans (Formula.closed_env_l φ hf (by funext i; exact Fin.cases rfl (fun _ => rfl) i))
  simp only [Formula.satisfies_forall_iff] at tr
  exact ⟨fun h y hy => (hs ⟨y, hy⟩).mp (tr.mp (fun x => (hr x).mpr (h x.val x.property)) ⟨y, hy⟩),
    fun h x hx => (hr ⟨x, hx⟩).mp (tr.mpr (fun y => (hs y).mpr (h y.val y.property)) ⟨x, hx⟩)⟩

theorem spred_predicate_l (hZF : M.Models ZF) {ω X A Y B j x y} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hp : M.PairMember I x y j) : M.mem x A ↔ M.mem y B := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  let x' : (smdl_structure_l I (R := R) hx.1.2.1).Domain := ⟨x, hj.1.1.input_mem_of_pairMember hp⟩
  let y' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨y, hj.1.1.output_mem_of_pairMember hp⟩
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj (n := 1) (.mem (.bound 0) (.bound 0))
    (by simp [Definitional.Formula.FreeClosed]) ⟨fun _ => x', fun _ => x'⟩ ⟨fun _ => y', fun _ => y'⟩ (fun _ => hp)
  simp only [Formula.satisfies_mem_iff] at tr
  exact (spred_read_l I (ZF.modelsKP hZF) hx x x).1.symm.trans (tr.trans
    (spred_read_l I (ZF.modelsKP hZF) hy y y).1)

/-- 谓词自身的传递性由扩张语言的初等性保持，不能只用遗忘谓词后的嵌入代替。 -/
theorem spred_transitive_l (hZF : M.Models ZF) {ω X A Y B j} (hω : M.IsOmega ω)
    (h : Spred_emb_d I ω X A Y B j) (hY : M.TransitiveSet Y) (hA : M.TransitiveSet A) : M.TransitiveSet B := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  obtain ⟨x, hxX⟩ := hx.1.2.1
  obtain ⟨y, hyY⟩ := hy.1.2.1
  let φ : Formula 1 0 := .forallE (.forallE (.imp
    (.conj (.mem .newest .newest) (.conj (.mem (.bound 1) .newest) (.neg (.mem .newest (.bound 1)))))
    (.mem (.bound 1) (.bound 1))))
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj φ (by simp [φ, Definitional.Formula.FreeClosed])
    ⟨Fin.elim0, fun _ => ⟨x, hxX⟩⟩ ⟨Fin.elim0, fun _ => ⟨y, hyY⟩⟩ (fun i => Fin.elim0 i)
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff] at tr
  have hs := tr.mp (fun a b hb => (spred_read_l I (ZF.modelsKP hZF) hx a.val a.val).1.mpr
    (hA b.val ((spred_read_l I (ZF.modelsKP hZF) hx b.val b.val).1.mp hb.1) a.val
      ((spred_mem_l I (ZF.modelsKP hZF) hx a.property b.property).mp hb.2)))
  intro b hb a hab
  let b' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨b, hy.2.1 b hb⟩
  let a' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨a, hY b b'.property a hab⟩
  exact (spred_read_l I (ZF.modelsKP hZF) hy a a).1.mp (hs a' b'
    ⟨(spred_read_l I (ZF.modelsKP hZF) hy b b).1.mpr hb,
      (spred_mem_l I (ZF.modelsKP hZF) hy a'.property b'.property).mpr hab⟩)

section
variable (hZF : M.Models ZF) {ω X A Y B j : M.Domain} (hω : M.IsOmega ω)
  (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
include hZF hω h hX hY

theorem spred_entry_l {a a' b b' F F'} (ha : M.PairMember I a a' j)
    (hb : M.PairMember I b b' j) (hF : M.PairMember I F F' j) : Rd_entry_d a b F ↔ Rd_entry_d a' b' F' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 3) (rd_entry0_m (.bound 2) (.bound 1) (.bound 0))
    (rd_entry0_m_freeClosed _ _ _ rfl rfl rfl) (rd_entry0_delta_l ..)
    ⟨Fin.cases F (Fin.cases b (fun _ => a)), fun _ => a⟩
    ⟨Fin.cases F' (Fin.cases b' (fun _ => a')), fun _ => a'⟩
    (Fin.cases hF (Fin.cases hb (fun _ => ha)))
  simp only [rd_entry0_sat_l hZF.1] at tr
  exact tr

theorem spred_function_l {D D' U U' F F'} (hD : M.PairMember I D D' j)
    (hU : M.PairMember I U U' j) (hF : M.PairMember I F F' j) : Fn0_d D U F ↔ Fn0_d D' U' F' := by
  have tr := spred_delta_l I hZF hω h hX hY (n := 3) (fn0_m (.bound 2) (.bound 1) (.bound 0))
    (fn0_m_freeClosed _ _ _ rfl rfl rfl) (fn0_delta_l ..)
    ⟨Fin.cases F (Fin.cases U (fun _ => D)), fun _ => D⟩
    ⟨Fin.cases F' (Fin.cases U' (fun _ => D')), fun _ => D'⟩
    (Fin.cases hF (Fin.cases hU (fun _ => hD)))
  simp only [fn0_sat_l hZF.1] at tr
  exact tr

end

end YesMetaZFC.SetTheory.Internal

/-! ## 传递成员结构间的有界公式与自然数保持

空谓词把纯成员嵌入接到既有公式传输。ω 的 Δ₀ 遗传有限性刻画保证其像
仍是背景的同一个 ω，不要求模型在外部标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smem_d.empty_pred_l {c X R z : M.Domain} (hm : Smem_d I c X R)
    (hz : ∀ x, ¬ M.mem x z) : Spred_d I c X z R :=
  ⟨hm.1, fun x hx => (hz x hx).elim, fun x y => (hm.2 x y).trans (and_congr_right fun _ => and_congr_right fun _ =>
    ⟨Or.inl, fun h => h.elim id (fun h => (hz x h.2).elim)⟩)⟩

theorem smap_delta_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    {n} (φ : Formula 1 n) (hf : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) q) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact spred_delta_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hq⟩ hX hY φ hf hd ρ η hp

theorem Smap_d.omega_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) : M.PairMember I ω ω q := by
  obtain ⟨ω₀, hω₀, finite⟩ := KPi.exists_omega_l (ZF.models_kpi_l hZF)
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  obtain ⟨Ω, _, hωΩ⟩ := hq.1.1.2.2 ω hωX
  have transfer := smap_delta_l I hZF hω hX hY hm hn hq (n := 1) (omega0_m (.bound 0))
    (by simp -implicitDefEqProofs) (omega0_delta_l _) ⟨fun _ => ω, fun _ => ω⟩ ⟨fun _ => Ω, fun _ => Ω⟩ (fun _ => hωΩ)
  simp only [omega0_sat_l hZF.1] at transfer
  have hΩ := transfer.mp ⟨hω.1, fun n hn => (finite n).mp hn⟩
  have eq := hZF.1.eq_of_same_members Ω ω (fun n =>
    ⟨fun hn => KPi.n0_in_inductive_l (ZF.models_kpi_l hZF) hω.1 (hΩ.2 n hn), hω.2 Ω hΩ.1 n⟩)
  exact eq ▸ hωΩ

end YesMetaZFC.SetTheory.Internal

/-! ## 谓词截面的初等像

截面由集合分离实际生成。扩张语言的全称公式把它的定义送到目标载体的
全部元素，因而也控制不在嵌入像中的新参数；逐点谓词保持不足以代替这一步。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 若 t=A∩D，则 j(t)=B∩j(D)；右侧量化目标中的全部对象。 -/
theorem spred_trace_l (hZF : M.Models ZF) {ω X A Y B j D D' t t' : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hY : M.TransitiveSet Y)
    (hD : M.PairMember I D D' j) (ht : M.PairMember I t t' j)
    (trace : ∀ x, M.mem x t ↔ M.mem x D ∧ M.mem x A) :
    ∀ y, M.mem y t' ↔ M.mem y D' ∧ M.mem y B := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  let φ : Formula 1 2 := .forallE (.iff
    (.conj (.mem .newest (.bound 1)) (.neg (.mem (.bound 1) .newest)))
    (.conj (.conj (.mem .newest (.bound 2)) (.neg (.mem (.bound 2) .newest)))
      (.mem .newest .newest)))
  let D₀ : (smdl_structure_l I (R := R) hx.1.2.1).Domain := ⟨D, hj.1.1.input_mem_of_pairMember hD⟩
  let t₀ : (smdl_structure_l I (R := R) hx.1.2.1).Domain := ⟨t, hj.1.1.input_mem_of_pairMember ht⟩
  let D₁ : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨D', hj.1.1.output_mem_of_pairMember hD⟩
  let t₁ : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨t', hj.1.1.output_mem_of_pairMember ht⟩
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj φ (by simp [φ, Definitional.Formula.FreeClosed])
    ⟨Fin.cases t₀ (fun _ => D₀), fun _ => t₀⟩ ⟨Fin.cases t₁ (fun _ => D₁), fun _ => t₁⟩
    (Fin.cases ht (fun _ => hD))
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff] at tr
  have read (x : (smdl_structure_l I (R := R) hx.1.2.1).Domain) :=
    (spred_mem_l I (ZF.modelsKP hZF) hx x.property t₀.property).trans ((trace x.val).trans
      (and_congr (spred_mem_l I (ZF.modelsKP hZF) hx x.property D₀.property).symm
        (spred_read_l I (ZF.modelsKP hZF) hx x.val x.val).1.symm))
  have target := tr.mp read
  intro y
  have owned : M.mem y t' ∨ M.mem y D' → M.mem y Y :=
    fun hh => hh.elim (hY t' t₁.property y) (hY D' D₁.property y)
  constructor
  · intro hy'
    let y' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨y, owned (Or.inl hy')⟩
    have hh := (target y').mp ((spred_mem_l I (ZF.modelsKP hZF) hy y'.property t₁.property).mpr hy')
    exact ⟨(spred_mem_l I (ZF.modelsKP hZF) hy y'.property D₁.property).mp hh.1,
      (spred_read_l I (ZF.modelsKP hZF) hy y y).1.mp hh.2⟩
  · rintro ⟨hyD, hyB⟩
    let y' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨y, owned (Or.inr hyD)⟩
    exact (spred_mem_l I (ZF.modelsKP hZF) hy y'.property t₁.property).mp ((target y').mpr
      ⟨(spred_mem_l I (ZF.modelsKP hZF) hy y'.property D₁.property).mpr hyD,
        (spred_read_l I (ZF.modelsKP hZF) hy y y).1.mpr hyB⟩)

end YesMetaZFC.SetTheory.Internal
