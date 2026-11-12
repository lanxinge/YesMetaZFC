import YesMetaZFC.Model.SetTheory.Source.Basic
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.Model.SetTheory.Reflection.SkolemSyntax

/-! # 内部公式程序的可组合构造

每次构造返回实际合法程序、旧程序的精确前缀及新根位置。布尔构造复用或非
指令，语义规格对任意模型与赋值同时成立；没有把预期真值作为构造假设。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Sbuild_d (ω n F m G k : M.Domain) : Prop where
  program : Sfm_d I ω m G
  cut : M.IsRestrictionOf I F G n
  span : M.MemberSubset n m
  root : M.mem k m

theorem Sbuild_d.comp {ω n F m G k l H r} (h : Sbuild_d I ω n F m G k)
    (g : Sbuild_d I ω m G l H r) : Sbuild_d I ω n F l H r := by
  refine ⟨g.program, ⟨h.cut.1, fun i a => ?_⟩, fun i hi => g.span i (h.span i hi), g.root⟩
  exact (h.cut.2 i a).trans ⟨fun hi => ⟨hi.1, ((g.cut.2 i a).mp hi.2).2⟩,
    fun hi => ⟨hi.1, (g.cut.2 i a).mpr ⟨h.span i hi.1, hi.2⟩⟩⟩

theorem Sbuild_d.sat_l (hZF : M.Models ZF) {ω n F m G k i} (hF : Sfm_d I ω n F)
    (h : Sbuild_d I ω n F m G k) (hi : M.mem i n) (X R E f : M.Domain) :
    Ssat_d I X R E F n i f ↔ Ssat_d I X R E G m i f := ssat_prefix_l I hZF hF h.program h.cut hi f

theorem sfm_node_build_l (hZF : M.Models ZF) {ω n F c} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hc : Sfm_node_d I ω n c) :
    ∃ m G, Sbuild_d I ω n F m G n ∧ M.PairMember I n c G := by
  obtain ⟨m, G, hm, hG, he⟩ := sfm_append_l I hZF hω hF hc
  have hp := sfm_append_prefix_l I hZF hF he
  exact ⟨m, G, ⟨hG, hp, sfm_prefix_subset_l I hF hG hp, hm.predecessor_mem⟩,
    (he n c).mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem sfm_rel_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j ω) : ∃ m G,
    Sbuild_d I ω n F m G n ∧ ∀ X R E f x y, M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I i x f → M.PairMember I j y f → (Ssat_d I X R E G m n f ↔ M.PairMember I x y R) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 i j
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inl ⟨i, j, hc, hi, hj⟩)
  refine ⟨m, G, h, fun X R E f x y hE hf hix hjy => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  exact ssat_rel_l I hZF h.program hH he hc hE hf hix hjy

/-- 真正的对象等号指令；不把成员外延等同预先解释为等号。 -/
theorem sfm_eq_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j ω) : ∃ m G,
    Sbuild_d I ω n F m G n ∧ ∀ X R E f x y, M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I i x f → M.PairMember I j y f → (Ssat_d I X R E G m n f ↔ x = y) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 1 i j
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inl ⟨i, j, hc, hi, hj⟩))
  refine ⟨m, G, h, fun X R E f x y hE hf hix hjy => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  exact ssat_eq_l I hZF h.program hH he hc hE hf hix hjy

theorem sfm_nor_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ ¬ (Ssat_d I X R E F n i f ∨ Ssat_d I X R E F n j f)) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 2 i j
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inr (Or.inl ⟨i, j, hc, hi, hj⟩)))
  refine ⟨m, G, n, h, fun X R E f hf => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  exact (ssat_nor_l I hZF h.program hH he hc hf).trans
    (not_congr (or_congr (h.sat_l I hZF hF hi X R E f).symm (h.sat_l I hZF hF hj X R E f).symm))

theorem sfm_neg_l (hZF : M.Models ZF) {ω n F i} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ ¬ Ssat_d I X R E F n i f) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_nor_l I hZF hω hF hi hi
  exact ⟨m, G, k, h, fun X R E f hf => (he X R E f hf).trans (not_congr ⟨fun h => h.elim id id, Or.inl⟩)⟩

theorem sfm_or_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ Ssat_d I X R E F n i f ∨ Ssat_d I X R E F n j f) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_nor_l I hZF hω hF hi hj
  obtain ⟨l, H, r, g, hg⟩ := sfm_neg_l I hZF hω h.program h.root
  refine ⟨l, H, r, h.comp I g, fun X R E f hf => ?_⟩
  exact (hg X R E f hf).trans ((not_congr (he X R E f hf)).trans Classical.not_not)

theorem sfm_and_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ Ssat_d I X R E F n i f ∧ Ssat_d I X R E F n j f) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_neg_l I hZF hω hF hi
  obtain ⟨l, H, r, g, hg⟩ := sfm_neg_l I hZF hω h.program (h.span j hj)
  obtain ⟨v, J, s, b, hb⟩ := sfm_nor_l I hZF hω g.program (g.span k h.root) g.root
  refine ⟨v, J, s, (h.comp I g).comp I b, fun X R E f hf => ?_⟩
  rw [hb X R E f hf, ← g.sat_l I hZF h.program h.root X R E f, he X R E f hf,
    hg X R E f hf, ← h.sat_l I hZF hF hj X R E f]
  classical
  simp only [not_or, Classical.not_not]

theorem sfm_imp_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ (Ssat_d I X R E F n i f → Ssat_d I X R E F n j f)) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_neg_l I hZF hω hF hi
  obtain ⟨l, H, r, g, hg⟩ := sfm_or_l I hZF hω h.program h.root (h.span j hj)
  refine ⟨l, H, r, h.comp I g, fun X R E f hf => ?_⟩
  rw [hg X R E f hf, he X R E f hf, ← h.sat_l I hZF hF hj X R E f]
  classical
  exact ⟨fun h hp => h.elim (fun hn => (hn hp).elim) id, fun h => by
    by_cases hp : Ssat_d I X R E F n i f
    · exact Or.inr (h hp)
    · exact Or.inl hp⟩

theorem sfm_iff_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ (Ssat_d I X R E F n i f ↔ Ssat_d I X R E F n j f)) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_imp_l I hZF hω hF hi hj
  obtain ⟨l, H, r, g, hg⟩ := sfm_imp_l I hZF hω h.program (h.span j hj) (h.span i hi)
  obtain ⟨v, J, s, b, hb⟩ := sfm_and_l I hZF hω g.program (g.span k h.root) g.root
  refine ⟨v, J, s, (h.comp I g).comp I b, fun X R E f hf => ?_⟩
  rw [hb X R E f hf, ← g.sat_l I hZF h.program h.root X R E f, he X R E f hf,
    hg X R E f hf, ← h.sat_l I hZF hF hj X R E f, ← h.sat_l I hZF hF hi X R E f]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem sfm_ex_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ ∃ x g,
        M.mem x X ∧ Senv_update_d I f i x g ∧ Ssat_d I X R E F n j g) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 3 i j
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inr (Or.inr ⟨i, j, hc, hi, hj⟩)))
  refine ⟨m, G, n, h, fun X R E f hf => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  exact (ssat_exists_l I hZF h.program hH he hc hf).trans (exists_congr fun x => exists_congr fun g =>
    and_congr_right fun _ => and_congr_right fun _ => (h.sat_l I hZF hF hj X R E g).symm)

/-- 全称量词由或非与存在指令构造，规格覆盖每个实际单坐标更新。 -/
theorem sfm_all_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.IsFunctionSpace I E ω X → M.mem f E →
      (Ssat_d I X R E G m k f ↔ ∀ x g, M.mem x X → Senv_update_d I f i x g → Ssat_d I X R E F n j g) := by
  obtain ⟨m, G, k, h, ht⟩ := sfm_neg_l I hZF hω hF hj
  obtain ⟨l, H, r, a, ha⟩ := sfm_ex_l I hZF hω h.program hi h.root
  obtain ⟨v, J, s, b, hb⟩ := sfm_neg_l I hZF hω a.program a.root
  refine ⟨v, J, s, (h.comp I a).comp I b, fun X R E f hE hf => ?_⟩
  rw [hb X R E f hf, ha X R E f hf]
  constructor
  · intro hn x g hx hu
    apply Classical.byContradiction
    exact fun hg => hn ⟨x, g, hx, hu,
      (ht X R E g ((hE g).mpr (hu.function_l I ((hE f).mp hf) hi hx))).mpr hg⟩
  · rintro hh ⟨x, g, hx, hu, hg⟩
    exact (ht X R E g ((hE g).mpr (hu.function_l I ((hE f).mp hf) hi hx))).mp hg (hh x g hx hu)

end YesMetaZFC.SetTheory.Internal

/-! ## 原 AST 编译的参数与量词语义

编译证书同时覆盖全部内部集合结构。参数对应只读取赋值图；量词绑定一个
未使用的内部编号，更新图仍属于完整赋值空间。源语义始终是原生产 AST 的语义。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Scompile_d {a d} (ω n F k : M.Domain) (v : Fin d → M.Domain) (φ : Formula a d) : Prop :=
  ∀ X R (hX : ∃ x, M.mem x X) E, M.IsFunctionSpace I E ω X → ∀ f, M.mem f E →
    ∀ ρ : Env (smdl_structure_l I (R := R) hX) d, (∀ i, M.PairMember I (v i) (ρ.bound i).val f) →
      (Ssat_d I X R E F n k f ↔ Definitional.Semantics.satisfies Semantics.interpretation ρ φ)

theorem Scompile_d.extend_l (hZF : M.Models ZF) {a d ω n F m G k r v} {φ : Formula a d}
    (hF : Sfm_d I ω n F) (h : Scompile_d I ω n F k v φ) (hb : Sbuild_d I ω n F m G r)
    (hk : M.mem k n) : Scompile_d I ω m G k v φ := by
  intro X R hX E hE f hf ρ hρ
  exact (hb.sat_l I hZF hF hk X R E f).symm.trans (h X R hX E hE f hf ρ hρ)

theorem scompile_neg_l (hZF : M.Models ZF) {a d ω n F k v} {φ : Formula a d}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hk : M.mem k n) (h : Scompile_d I ω n F k v φ) :
    ∃ m G r, Sbuild_d I ω n F m G r ∧ Scompile_d I ω m G r v (.neg φ) := by
  obtain ⟨m, G, r, hb, he⟩ := sfm_neg_l I hZF hω hF hk
  refine ⟨m, G, r, hb, fun X R hX E hE f hf ρ hρ => ?_⟩
  simpa only [Definitional.Semantics.satisfies] using
    (he X R E f hf).trans (not_congr (h X R hX E hE f hf ρ hρ))

/-- 新变量不覆盖参数时，存在量词的程序构造与原 AST 的量词精确对应。 -/
theorem scompile_ex_l (hZF : M.Models ZF) {a d ω n F k i} {v : Fin d → M.Domain} {φ : Formula a (d+1)}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hk : M.mem k n) (hi : M.mem i ω)
    (hv : ∀ j, v j ≠ i) (h : Scompile_d I ω n F k (Fin.cases i v) φ) :
    ∃ m G r, Sbuild_d I ω n F m G r ∧ Scompile_d I ω m G r v (.existsE φ) := by
  obtain ⟨m, G, r, hb, he⟩ := sfm_ex_l I hZF hω hF hi hk
  refine ⟨m, G, r, hb, fun X R hX E hE f hf ρ hρ => ?_⟩
  have params {x g} (hx : M.mem x X) (hg : Senv_update_d I f i x g) :
      ∀ j, M.PairMember I (Fin.cases i v j) ((ρ.push ⟨x, hx⟩).bound j).val g :=
    Fin.cases ((hg.2 i x).mpr (Or.inl ⟨rfl, rfl⟩))
      (fun j => (hg.2 (v j) (ρ.bound j).val).mpr (Or.inr ⟨hv j, hρ j⟩))
  refine (he X R E f hf).trans ?_
  simp only [Definitional.Semantics.satisfies]
  constructor
  · rintro ⟨x, g, hx, hg, hh⟩
    have hgE := (hE g).mpr (hg.function_l I ((hE f).mp hf) hi hx)
    exact ⟨⟨x, hx⟩, (h X R hX E hE g hgE (ρ.push ⟨x, hx⟩) (params hx hg)).mp hh⟩
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg, hgE⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi x.property
    exact ⟨x.val, g, x.property, hg,
      (h X R hX E hE g ((hE g).mpr hgE) (ρ.push x) (params x.property hg)).mpr hx⟩

/-- 任意有限参数赋值均由模型内实际函数图实现，不要求外部参数函数属于模型。 -/
theorem senv_params_l (hZF : M.Models ZF) {ω X E} (hE : M.IsFunctionSpace I E ω X)
    (hX : ∃ x, M.mem x X) {d} (v p : Fin d → M.Domain)
    (hv : Function.Injective v) (hvω : ∀ i, M.mem (v i) ω) (hp : ∀ i, M.mem (p i) X) :
    ∃ f, M.mem f E ∧ ∀ i, M.PairMember I (v i) (p i) f := by
  induction d with
  | zero =>
    obtain ⟨x, hx⟩ := hX
    obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := ω) hx
    exact ⟨f, (hE f).mpr hf, fun i => Fin.elim0 i⟩
  | succ d ih =>
    obtain ⟨f, hf, he⟩ := ih (fun i => v i.succ) (fun i => p i.succ)
      (fun i j hij => Fin.ext (by have hh := congrArg Fin.val (hv hij); simp only [Fin.val_succ] at hh; omega))
      (fun i => hvω i.succ) (fun i => hp i.succ)
    obtain ⟨g, hg, hG⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hvω 0) (hp 0)
    refine ⟨g, (hE g).mpr hG, Fin.cases ((hg.2 (v 0) (p 0)).mpr (Or.inl ⟨rfl, rfl⟩)) ?_⟩
    intro i
    exact (hg.2 (v i.succ) (p i.succ)).mpr (Or.inr ⟨fun h => Fin.succ_ne_zero i (hv h), he i⟩)

end YesMetaZFC.SetTheory.Internal

/-! ## 原 Project 公式的内部编译

结构归纳只用于输入的原 AST；输出始终是模型内的实际合法指令图。每一步
保留旧程序并给出对全部集合结构的语义证书，量词的新编号由内部后继取得。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

private theorem true_compile_l (hZF : M.Models ZF) {d ω σ n F} (hω : M.IsOmega ω)
    (v : Fin d → M.Domain) (hσ : M.mem σ ω) (hF : Sfm_d I ω n F) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ Scompile_d I ω m G k v (.truth : Formula 0 d) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 1 σ σ
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inl ⟨σ, σ, hc, hσ, hσ⟩))
  refine ⟨m, G, n, h, fun X R hX E hE f hf ρ _ => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 σ hσ
  simp only [Definitional.Semantics.satisfies]
  exact (ssat_eq_l I hZF h.program hH he hc hE hf hx hx).trans ⟨fun _ => trivial, fun _ => rfl⟩

/-- 在任意已有合法程序后编译第 0 层 AST；同一输出对所有模型及参数赋值有效。 -/
theorem source_compile_core_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω)
    {d} (φ : Formula 0 d) (hφ : φ.FreeClosed) {σ n F} (v : Fin d → M.Domain)
    (hσ : M.mem σ ω) (hv : ∀ i, M.mem (v i) σ) (hF : Sfm_d I ω n F) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ Scompile_d I ω m G k v φ := by
  induction φ generalizing σ n F <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case truth => exact true_compile_l I hZF hω v hσ hF
  case falsum =>
    obtain ⟨m, G, k, h, hc⟩ := true_compile_l I hZF hω v hσ hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_neg_l I hZF hω h.program h.root hc
    refine ⟨l, H, r, h.comp I g, fun X R hX E hE f hf ρ hρ => ?_⟩
    have he := hg X R hX E hE f hf ρ hρ
    simp only [Definitional.Semantics.satisfies] at he ⊢
    exact he.trans ⟨fun h => h True.intro, False.elim⟩
  case mem s t =>
    cases s with
    | free i => cases hφ.1
    | bound i =>
      cases t with
      | free j => cases hφ.2
      | bound j =>
        obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 (v i) (v j)
        obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF
          (Or.inl ⟨v i, v j, hc, hω.transitive (ZF.modelsKP hZF) σ hσ _ (hv i), hω.transitive (ZF.modelsKP hZF) σ hσ _ (hv j)⟩)
        refine ⟨m, G, n, h, fun X R hX E hE f hf ρ hρ => ?_⟩
        obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
        simp only [Definitional.Semantics.satisfies, Definitional.Term.eval]
        unfold smdl_structure_l
        exact ssat_rel_l I hZF h.program hH he hc hE hf (hρ i) (hρ j)
  case atom r hr ts =>
    have hh : (0 : Nat) < 0 := hr
    omega
  case neg φ ih =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ v hσ hv hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_neg_l I hZF hω h.program h.root hc
    exact ⟨l, H, r, h.comp I g, hg⟩
  case conj φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_and_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (and_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case disj φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_or_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (or_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case imp φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_imp_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (imp_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case iff φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_iff_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (iff_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case existsE φ ih =>
    obtain ⟨τ, ht, htω⟩ := hω.1.2 σ hσ
    have hV : ∀ i, M.mem (Fin.cases σ v i) τ :=
      Fin.cases ht.predecessor_mem (fun i => (ht (v i)).mpr (Or.inl (hv i)))
    obtain ⟨m, G, k, h, hc⟩ := ih hφ (Fin.cases σ v) htω hV hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_ex_l I hZF hω h.program h.root hσ
      (fun i hi => by
        have hh := hv i
        rw [hi] at hh
        exact KP.mem_irrefl_d (ZF.modelsKP hZF) σ hh) hc
    exact ⟨l, H, r, h.comp I g, hg⟩
  case forallE φ ih =>
    obtain ⟨τ, ht, htω⟩ := hω.1.2 σ hσ
    have hV : ∀ i, M.mem (Fin.cases σ v i) τ :=
      Fin.cases ht.predecessor_mem (fun i => (ht (v i)).mpr (Or.inl (hv i)))
    obtain ⟨m, G, k, h, hc⟩ := ih hφ (Fin.cases σ v) htω hV hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_neg_l I hZF hω h.program h.root hc
    obtain ⟨s, J, q, b, hb⟩ := scompile_ex_l I hZF hω g.program g.root hσ
      (fun i hi => by
        have hh := hv i
        rw [hi] at hh
        exact KP.mem_irrefl_d (ZF.modelsKP hZF) σ hh) hg
    obtain ⟨z, K, w, e, he⟩ := scompile_neg_l I hZF hω b.program b.root hb
    refine ⟨z, K, w, ((h.comp I g).comp I b).comp I e, fun X R hX E hE f hf ρ hρ => ?_⟩
    have hh := he X R hX E hE f hf ρ hρ
    simp only [Definitional.Semantics.satisfies] at hh ⊢
    exact hh.trans ⟨fun hn x => Classical.byContradiction (fun hx => hn ⟨x, hx⟩), fun h ⟨x, hx⟩ => hx (h x)⟩

/-- 原 AST 一次编译成实际内部公式码，并给出规范参数编号及全模型语义对应。 -/
theorem source_compile_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) {a d}
    (φ : Formula a d) (hφ : φ.FreeClosed) : ∃ c n F k, ∃ v : Fin d → M.Domain,
    Sformula_d I ω c n F k ∧ (∀ i, Num_d i.val (v i)) ∧ Scompile_d I ω n F k v φ := by
  -- 有限组数码只在存在命题中取见证，不从存在性证明提取模型数据。
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i : Fin d => num_exists_l (ZF.modelsKP hZF) i.val)
  obtain ⟨σ, hσ⟩ := num_exists_l (ZF.modelsKP hZF) d
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hf : Sfm_d I ω e e := ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he),
    Structure.IsSequenceOfLength.empty I he, fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
  obtain ⟨n, F, k, h, hc⟩ := source_compile_core_l I hZF hω (source_core_l φ) (source_core_closed_l φ hφ)
    v (num_mem_l hZF.1 hω hσ) (fun i => num_lt_l hZF.1 (hv i) hσ i.isLt) hf
  obtain ⟨c, hcF⟩ := I.total F k
  exact ⟨c, n, F, k, v, ⟨hcF, h.program, h.root⟩, hv,
    fun X R hX E hE f hf ρ hρ => (hc X R hX E hE f hf ρ hρ).trans (source_core_sat_l φ ρ)⟩

/-- 指定编码模型及原公式参数后，自动生成公式码、内部赋值和精确满足等价式。 -/
theorem source_satisfaction_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) {d} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) hM.2.1) d) : ∃ a E f,
      (∃ n F k, Sformula_d I ω a n F k) ∧ M.IsFunctionSpace I E ω X ∧ M.mem f E ∧
        (Satisfies_d I ω c a f ↔ Formula.satisfies ρ φ) := by
  obtain ⟨a, n, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  have hinj : Function.Injective v := by
    intro i j he
    have hj := hv j
    rw [← he] at hj
    exact Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) hj)
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hE hM.2.1 v (fun i => (ρ.bound i).val) hinj
    (fun i => num_mem_l hZF.1 hω (hv i)) (fun i => (ρ.bound i).property)
  exact ⟨a, E, f, ⟨n, F, k, ha⟩, hE, hf,
    (satisfies_decode_l I hZF.1 hM ha hE).trans (hc X R hM.2.1 E hE f hf ρ hp)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原变量中一个内部有限区间的成员枚举

编译“x 等于某个非首坐标”的有限析取。沿模型自己的 ω 归纳，
输出仍为原程序；不把变量列重新打包，也不固定标签的排列次序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sg_any_d (ω e b n m G u : M.Domain) : Prop := ∀ X R E f x,
  M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I b x f →
    (Ssat_d I X R E G m u f ↔ ∃ i, M.mem i n ∧ i ≠ e ∧ M.PairMember I i x f)

def sg_any_m {d} (ω e b n m G u : Term d) : Formula 1 d := set[d] ⟪∀ X R E f x,
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E, ⌜ω⌝ₛ, X) → f ∈ E → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ, x, f) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔
      (∃ i ∈ ⌜n⌝ₛ, ¬ (i = ⌜e⌝ₛ) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, x, f)))⟫

@[simp] theorem sg_any_closed_l {d} (ω e b n m G u : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hb : b.freeSupport = [])
    (hn : n.freeSupport = []) (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (sg_any_m (𝒞 := 𝒞) ω e b n m G u).FreeClosed := by
  simp -implicitDefEqProofs [sg_any_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hw, he, hb, hn, hm, hG, hu]

theorem sg_any_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω e b n m G u : Term d) :
    Formula.satisfies ρ (sg_any_m (𝒞 := 𝒞) ω e b n m G u) ↔
      Sg_any_d I (ω.eval ρ) (e.eval ρ) (b.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [sg_any_m, Sg_any_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]
  rfl

theorem sg_any_build_l (hZF : M.Models ZF) {ω e b n : M.Domain}
    (hω : M.IsOmega ω) (hb : M.mem b ω) (hn : M.mem n ω) :
    ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_any_d I ω e b n m G u := by
  let ρ : Env M 3 := ⟨Fin.cases b (Fin.cases e (fun _ => ω)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := .existsE (.existsE (.existsE (.conj
    (sfm_m (𝒞 := 𝒞) (.bound 6) (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 2))
      (sg_any_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))) }
  have sat k : φ.denote ρ k ↔ ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_any_d I ω e b k m G u := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sfm_sat_l I hZF.1, Formula.satisfies_mem_iff, sg_any_sat_l I hZF.1]
    rfl
  apply (sat n).mp
  apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
  · intro z hz
    have empty : Sfm_d I ω z z := ⟨num_mem_l hZF.1 hω (show Num_d 0 z from hz),
      Structure.IsSequenceOfLength.empty I hz, fun _ _ h => h.elim fun p hp => (hz p hp.2).elim⟩
    obtain ⟨m, G, add, eq⟩ := sfm_eq_l I hZF hω empty hb hb
    obtain ⟨l, H, u, neg, read⟩ := sfm_neg_l I hZF hω add.program add.root
    refine (sat z).mpr ⟨l, H, u, neg.program, neg.root, fun X R E f x hE hf hx => ?_⟩
    exact (read X R E f hf).trans ((not_congr (eq X R E f x x hE hf hx hx)).trans
      (iff_of_false (fun h => h rfl) (fun ⟨i, hi, _⟩ => hz i hi)))
  · intro k hk ih l succ
    obtain ⟨m, G, u, prog, hu, all⟩ := (sat k).mp ih
    by_cases hke : k = e
    · refine (sat l).mpr ⟨m, G, u, prog, hu, fun X R E f x hE hf hx => (all X R E f x hE hf hx).trans ?_⟩
      exact ⟨fun ⟨i, hi, ne, hx⟩ => ⟨i, (succ i).mpr (Or.inl hi), ne, hx⟩,
        fun ⟨i, hi, ne, hx⟩ => ⟨i, ((succ i).mp hi).elim id
          (fun eq => (ne ((hZF.1.eq_of_same_members i k eq).trans hke)).elim), ne, hx⟩⟩
    obtain ⟨m₁, G₁, add, eq⟩ := sfm_eq_l I hZF hω prog hb hk
    obtain ⟨m₂, G₂, v, disj, both⟩ := sfm_or_l I hZF hω add.program (add.span u hu) add.root
    refine (sat l).mpr ⟨m₂, G₂, v, disj.program, disj.root, fun X R E f x hE hf hx => ?_⟩
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 k hk
    have old := (add.sat_l I hZF prog hu X R E f).symm.trans (all X R E f x hE hf hx)
    refine (both X R E f hf).trans ((or_congr old (eq X R E f x y hE hf hx hy)).trans ⟨?_, ?_⟩)
    · rintro (⟨i, hi, ne, hx⟩ | eq)
      · exact ⟨i, (succ i).mpr (Or.inl hi), ne, hx⟩
      · exact ⟨k, succ.predecessor_mem, hke, eq.symm ▸ hy⟩
    · rintro ⟨i, hi, ne, hx⟩
      rcases (succ i).mp hi with hi | eq
      · exact Or.inl ⟨i, hi, ne, hx⟩
      · exact Or.inr (((hE f).mp hf).1.2 k x y (hZF.1.eq_of_same_members i k eq ▸ hx) hy)

end YesMetaZFC.SetTheory.Internal

/-! ## 限制编译的纯语法证书

规则只检查原指令、新指令和旧根到新根的图。存在量词展开为
∃vᵢ( vᵢ∈v_b ∧ ψ )，其中合取由两次取反和一次或非编码。
证书不包含任何预设的真值保持断言。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_at_d (k : Nat) (G r i j : M.Domain) : Prop := ∃ c, M.PairMember I r c G ∧ Sop_d I k c i j
def sr_at_m (k : Nat) {d} (G r i j : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 r.weaken .newest G.weaken) (sop_m (𝒞 := 𝒞) k .newest i.weaken j.weaken))
derive_free_closed sr_at_m

theorem sr_at_sat_l (k : Nat) {d} (ρ : Env M d) (G r i j : Term d) :
    Formula.satisfies ρ (sr_at_m (𝒞 := 𝒞) k G r i j) ↔ Sr_at_d I k (G.eval ρ) (r.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [sr_at_m, Sr_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, sop_sat_l I, Definitional.Term.eval_weaken]; rfl

def Sr_rule_d (b T G c u : M.Domain) : Prop :=
  (∃ i j, Sop_d I 0 c i j ∧ Sr_at_d I 0 G u i j) ∨
  (∃ i j, Sop_d I 1 c i j ∧ Sr_at_d I 1 G u i j) ∨
  (∃ i j v w, Sop_d I 2 c i j ∧ M.PairMember I i v T ∧ M.PairMember I j w T ∧ Sr_at_d I 2 G u v w) ∨
  ∃ i j v a p q t, Sop_d I 3 c i j ∧ M.PairMember I j v T ∧ Sr_at_d I 0 G a i b ∧
    Sr_at_d I 2 G p a a ∧ Sr_at_d I 2 G q v v ∧ Sr_at_d I 2 G t p q ∧ Sr_at_d I 3 G u i t

def sr_rule_m {d} (b T G c u : Term d) : Formula 1 d := set[d] ⟪
  (∃ i j, ⌜sop_m (𝒞 := 𝒞) 0⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, i, j)) ∨
  (∃ i j, ⌜sop_m (𝒞 := 𝒞) 1⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜sr_at_m (𝒞 := 𝒞) 1⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, i, j)) ∨
  (∃ i j v w, ⌜sop_m (𝒞 := 𝒞) 2⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, v, ⌜T⌝ₛ) ∧
    ⌜Formula.orderedPairMem 𝒞⌝ₚ(j, w, ⌜T⌝ₛ) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, v, w)) ∨
  (∃ i j v a p q t, ⌜sop_m (𝒞 := 𝒞) 3⌝ₚ(⌜c⌝ₛ, i, j) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(j, v, ⌜T⌝ₛ) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, a, i, ⌜b⌝ₛ) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, p, a, a) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, q, v, v) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, t, p, q) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, i, t))⟫
derive_free_closed sr_rule_m

theorem sr_rule_sat_l {d} (ρ : Env M d) (b T G c u : Term d) :
    Formula.satisfies ρ (sr_rule_m (𝒞 := 𝒞) b T G c u) ↔
      Sr_rule_d I (b.eval ρ) (T.eval ρ) (G.eval ρ) (c.eval ρ) (u.eval ρ) := by
  simp only [sr_rule_m, Sr_rule_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, sop_sat_l I, sr_at_sat_l I,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem Sr_at_d.extend_l {ω m G l H z r i j : M.Domain} {a : Nat}
    (h : Sr_at_d I a G r i j) (e : Sbuild_d I ω m G l H z) : Sr_at_d I a H r i j := by
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c, ((e.cut.2 r c).mp hc).2, hs⟩

theorem Sr_rule_d.mono_l {b T U G H c u : M.Domain} (h : Sr_rule_d I b T G c u)
    (map : ∀ i j, M.PairMember I i j T → M.PairMember I i j U)
    (program : ∀ i j, M.PairMember I i j G → M.PairMember I i j H) : Sr_rule_d I b U H c u := by
  have row {k r i j} (h : Sr_at_d I k G r i j) : Sr_at_d I k H r i j :=
    h.elim fun c h => ⟨c, program r c h.1, h.2⟩
  rcases h with ⟨i, j, hs, h⟩ | ⟨i, j, hs, h⟩ | ⟨i, j, v, w, hs, hi, hj, h⟩ |
    ⟨i, j, v, a, p, q, t, hs, hj, ha, hp, hq, ht, hu⟩
  · exact Or.inl ⟨i, j, hs, row h⟩
  · exact Or.inr (Or.inl ⟨i, j, hs, row h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, j, v, w, hs, map i v hi, map j w hj, row h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, j, v, a, p, q, t, hs, map j v hj, row ha, row hp, row hq, row ht, row hu⟩))

end YesMetaZFC.SetTheory.Internal

/-! ## 保留指令位置的程序追加

与语义构造器共享同一个原追加操作，额外返回实际新指令，供纯语法证书使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sr_rel_add_l (hZF : M.Models ZF) {ω m G i j} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hi : M.mem i ω) (hj : M.mem j ω) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I 0 H m i j := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 i j
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG (Or.inl ⟨i, j, hc, hi, hj⟩)
  exact ⟨l, H, h, c, row, hc⟩

theorem sr_nor_add_l (hZF : M.Models ZF) {ω m G i j} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hi : M.mem i m) (hj : M.mem j m) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I 2 H m i j := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 2 i j
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG (Or.inr (Or.inr (Or.inl ⟨i, j, hc, hi, hj⟩)))
  exact ⟨l, H, h, c, row, hc⟩

theorem sr_ex_add_l (hZF : M.Models ZF) {ω m G i j} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hi : M.mem i ω) (hj : M.mem j m) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I 3 H m i j := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 3 i j
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG (Or.inr (Or.inr (Or.inr ⟨i, j, hc, hi, hj⟩)))
  exact ⟨l, H, h, c, row, hc⟩

def Sr_and_d (G t u v : M.Domain) : Prop := ∃ a b,
  Sr_at_d I 2 G a u u ∧ Sr_at_d I 2 G b v v ∧ Sr_at_d I 2 G t a b

def sr_and_m {d} (G t u v : Term d) : Formula 1 d := set[d] ⟪∃ a b,
  ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, a, ⌜u⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, b, ⌜v⌝ₛ, ⌜v⌝ₛ) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, ⌜t⌝ₛ, a, b)⟫
derive_free_closed sr_and_m

theorem sr_and_sat_l {d} (ρ : Env M d) (G t u v : Term d) :
    Formula.satisfies ρ (sr_and_m (𝒞 := 𝒞) G t u v) ↔ Sr_and_d I (G.eval ρ) (t.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [sr_and_m, Sr_and_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sr_at_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem Sr_and_d.extend_l {ω m G l H z t u v : M.Domain} (h : Sr_and_d I G t u v)
    (e : Sbuild_d I ω m G l H z) : Sr_and_d I H t u v := by
  obtain ⟨a, b, ha, hb, ht⟩ := h
  exact ⟨a, b, ha.extend_l I e, hb.extend_l I e, ht.extend_l I e⟩

theorem sr_and_build_l (hZF : M.Models ZF) {ω m G u v} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hu : M.mem u m) (hv : M.mem v m) :
    ∃ l H t, Sbuild_d I ω m G l H t ∧ Sr_and_d I H t u v := by
  obtain ⟨m₁, G₁, h₁, a₁⟩ := sr_nor_add_l I hZF hω hG hu hu
  obtain ⟨m₂, G₂, h₂, a₂⟩ := sr_nor_add_l I hZF hω h₁.program (h₁.span v hv) (h₁.span v hv)
  obtain ⟨l, H, h₃, a₃⟩ := sr_nor_add_l I hZF hω h₂.program (h₂.span m h₁.root) h₂.root
  exact ⟨l, H, m₂, (h₁.comp I h₂).comp I h₃, m, m₁, a₁.extend_l I (h₂.comp I h₃), a₂.extend_l I h₃, a₃⟩

theorem Sr_and_d.correct_l (hZF : M.Models ZF) {ω G m t u v X R E f : M.Domain}
    (hG : Sfm_d I ω m G) (h : Sr_and_d I G t u v) (hf : M.mem f E) :
    Ssat_d I X R E G m t f ↔ Ssat_d I X R E G m u f ∧ Ssat_d I X R E G m v f := by
  obtain ⟨a, b, ha, hb, ht⟩ := h
  obtain ⟨ca, hca, oa⟩ := ha
  obtain ⟨cb, hcb, ob⟩ := hb
  obtain ⟨ct, hct, ot⟩ := ht
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G hG.2.1.1
  rw [ssat_nor_l I hZF hG hH hct ot hf, ssat_nor_l I hZF hG hH hca oa hf,
    ssat_nor_l I hZF hG hH hcb ob hf]
  simp only [or_self, not_or, Classical.not_not]

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部有限组变量的合取编译

沿内部 ω 实际追加成员指令及合取。归纳不变式使用可分离的满足关系公式，
输出仍是原合法程序；不把内部变量数换成宿主 Nat。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sg_all_d (ω b n m G u : M.Domain) : Prop := ∀ X R E f x,
  M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I b x f →
    (Ssat_d I X R E G m u f ↔ ∀ i y, M.mem i n → M.PairMember I i y f → M.PairMember I y x R)

def sg_all_m {d} (ω b n m G u : Term d) : Formula 1 d := set[d] ⟪∀ X R E f x,
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E, ⌜ω⌝ₛ, X) → f ∈ E → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ, x, f) →
  (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔
    (∀ i y, i ∈ ⌜n⌝ₛ → ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, y, f) → ⌜Formula.orderedPairMem 𝒞⌝ₚ(y, x, R)))⟫

@[simp] theorem sg_all_closed_l {d} (ω b n m G u : Term d)
    (hω : ω.freeSupport = []) (hb : b.freeSupport = []) (hn : n.freeSupport = [])
    (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (sg_all_m (𝒞 := 𝒞) ω b n m G u).FreeClosed := by
  simp -implicitDefEqProofs [sg_all_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hb, hn, hm, hG, hu]

theorem sg_all_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b n m G u : Term d) :
    Formula.satisfies ρ (sg_all_m (𝒞 := 𝒞) ω b n m G u) ↔
      Sg_all_d I (ω.eval ρ) (b.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [sg_all_m, Sg_all_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 自动编译所有 i<n 的关系断言 R(vᵢ,v_b)，允许内部非标准的 n。 -/
theorem sg_all_build_l (hZF : M.Models ZF) {ω b n : M.Domain}
    (hω : M.IsOmega ω) (hb : M.mem b ω) (hn : M.mem n ω) :
    ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_all_d I ω b n m G u := by
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => ω), fun _ => ω⟩
  let φ : UnarySchema 2 := { body := .existsE (.existsE (.existsE (.conj
    (sfm_m (𝒞 := 𝒞) (.bound 5) (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 2))
      (sg_all_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))) }
  have sat k : φ.denote ρ k ↔ ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_all_d I ω b k m G u := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sfm_sat_l I hZF.1, Formula.satisfies_mem_iff, sg_all_sat_l I hZF.1]; rfl
  apply (sat n).mp
  apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
  · intro e he
    have empty : Sfm_d I ω e e := ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he),
      Structure.IsSequenceOfLength.empty I he, fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
    obtain ⟨m, G, built, read⟩ := sfm_eq_l I hZF hω empty hb hb
    refine (sat e).mpr ⟨m, G, e, built.program, built.root, fun X R E f x hE hf hbx => ?_⟩
    exact (read X R E f x x hE hf hbx hbx).trans ⟨fun _ i _ hi => (he i hi).elim, fun _ => rfl⟩
  · intro k hk ih l succ
    obtain ⟨m, G, u, hG, hu, all⟩ := (sat k).mp ih
    obtain ⟨m₁, G₁, add, read⟩ := sfm_rel_l I hZF hω hG hk hb
    obtain ⟨m₂, G₂, v, conj, both⟩ := sfm_and_l I hZF hω add.program (add.span u hu) add.root
    refine (sat l).mpr ⟨m₂, G₂, v, conj.program, conj.root, fun X R E f x hE hf hbx => ?_⟩
    obtain ⟨y, hy, hky⟩ := ((hE f).mp hf).2.2 k hk
    have old := (add.sat_l I hZF hG hu X R E f).symm.trans (all X R E f x hE hf hbx)
    refine (both X R E f hf).trans ((and_congr old (read X R E f y x hE hf hky hbx)).trans ⟨?_, ?_⟩)
    · rintro ⟨prev, last⟩ i z hi hiz
      rcases (succ i).mp hi with hi | hi
      · exact prev i z hi hiz
      · have eq := hZF.1.eq_of_same_members i k hi
        subst i
        exact ((hE f).mp hf).1.2 k z y hiz hky ▸ last
    · intro full
      exact ⟨fun i z hi hiz => full i z ((succ i).mpr (Or.inl hi)) hiz, full k y succ.predecessor_mem hky⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原公式的有限参数编译

原公式只编译一次。参数存入实际内部有限函数，零号位置留给待定义对象；
列外统一取空集。语义证书同时覆盖全部包含参数的集合结构及全部候选对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 有限原参数产生内部公式码和参数列，证书对载体、关系及候选值统一成立。 -/
theorem source_finite_compile_l (hZF : M.Models ZF) {ω e B} (hω : M.IsOmega ω)
    (he : Num_d 0 e) (heB : M.mem e B) {d} (φ : Formula 1 (d+1)) (hφ : φ.FreeClosed)
    (p : Fin d → M.Domain) (hp : ∀ i, M.mem (p i) B) :
    ∃ a n s, (∃ m F k, Sformula_d I ω a m F k) ∧ M.mem n ω ∧
      M.IsSetFunctionFromTo I s n B ∧
      ∀ X c R (hM : Smdl_d I c X R), M.MemberSubset B X →
        ∀ η : Env (smdl_structure_l I (R := R) hM.2.1) d,
          (∀ i, (η.bound i).val = p i) → ∀ y : (smdl_structure_l I (R := R) hM.2.1).Domain,
            (Ssk_wit_d I ω c X e a e s y.val ↔ Formula.satisfies (η.push y) φ) := by
  obtain ⟨a, m, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨n, hn⟩ := num_exists_l (ZF.modelsKP hZF) (d+1)
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I n B
  have hinj : Function.Injective v := by
    intro i j h
    exact Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv j))
  obtain ⟨s, hsD, hs⟩ := senv_params_l I hZF hD ⟨e, heB⟩ v (Fin.cases e p) hinj
    (fun i => num_lt_l hZF.1 (hv i) hn i.isLt) (Fin.cases heB hp)
  have hsB := (hD s).mp hsD
  have hnω := num_mem_l hZF.1 hω hn
  have heω := num_mem_l hZF.1 hω he
  have hv0 : v 0 = e := num_unique_l hZF.1 (hv 0) he
  refine ⟨a, n, s, ⟨m, F, k, ha⟩, hnω, hsB, ?_⟩
  intro X c R hM hBX η hη y
  have hsX : M.IsSetFunctionFromTo I s n X :=
    ⟨hsB.1, hsB.2.1, fun i hi => (hsB.2.2 i hi).elim fun z hz => ⟨z, hBX z hz.1, hz.2⟩⟩
  obtain ⟨f, hf, hfX⟩ := senv_fill_exists_l I hZF hsX (hBX e heB)
  obtain ⟨g, hg, hgX⟩ := senv_update_exists_l I hZF hfX heω y.property
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine (ssk_wit_decode_l I hZF.1 hnω hsX hf hg).trans
    ((satisfies_decode_l I hZF.1 hM ha hE).trans
      (hc X R hM.2.1 E hE g ((hE g).mpr hgX) (η.push y) ?_))
  refine Fin.cases ?_ (fun i => ?_)
  · exact (hg.2 (v 0) y.val).mpr (Or.inl ⟨hv0, rfl⟩)
  · have hne : v i.succ ≠ e := by
      intro h
      have hh := num_injective_l (ZF.modelsKP hZF) (hv i.succ) (h.symm ▸ he)
      simp only [Fin.val_succ] at hh
      omega
    exact (hg.2 (v i.succ) (η.bound i).val).mpr (Or.inr ⟨hne,
      (hf.2 (v i.succ) (η.bound i).val).mpr ⟨num_mem_l hZF.1 hω (hv i.succ),
        Or.inl ⟨num_lt_l hZF.1 (hv i.succ) hn i.succ.isLt, (hη i).symm ▸ hs i.succ⟩⟩⟩)

end YesMetaZFC.SetTheory.Internal
