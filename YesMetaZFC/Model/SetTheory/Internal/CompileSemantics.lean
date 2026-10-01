import YesMetaZFC.Model.SetTheory.Internal.Builder

/-! # 原 AST 编译的参数与量词语义

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
