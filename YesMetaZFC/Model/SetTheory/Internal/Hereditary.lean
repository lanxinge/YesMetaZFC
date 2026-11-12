import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.Model.SetTheory.Reflection.SkolemSyntax
import YesMetaZFC.Model.SetTheory.Source.Elementary
import YesMetaZFC.Model.SetTheory.Sigma1Substructure
import YesMetaZFC.Model.SetTheory.Embedding.ElementarySyntax
import YesMetaZFC.SetTheory.Hereditary
import YesMetaZFC.SetTheory.Card.Properties.Basic

/-! # 内部隶属结构的解码与外延性

传递集合的成员都仍在载体中，因此其实际隶属结构保持外延性。这是一般内部
模型性质，不依赖力迫或名称定义。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c X R : M.Domain} (hM : Smdl_d I c X R)
  (hR : ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
local notation "L" => smdl_structure_l I (R := R) (And.left (And.right hM))
include hR

theorem smem_member_l (a b : (L).Domain) : (L).mem a b ↔ M.mem a.val b.val :=
  (hR a.val b.val).trans ⟨And.right ∘ And.right, fun h => ⟨a.property, b.property, h⟩⟩

theorem smem_ext_l (hX : M.TransitiveSet X) (hE : Extensional M) : Extensional L := by
  refine ⟨fun a b h => Subtype.ext (hE.eq_of_same_members a.val b.val (fun x => ?_))⟩
  constructor
  · intro hx
    let y : (L).Domain := ⟨x, hX a.val a.property x hx⟩
    exact (smem_member_l I hM hR y b).mp ((h y).mp ((smem_member_l I hM hR y a).mpr hx))
  · intro hx
    let y : (L).Domain := ⟨x, hX b.val b.property x hx⟩
    exact (smem_member_l I hM hR y a).mp ((h y).mpr ((smem_member_l I hM hR y b).mpr hx))

end YesMetaZFC.SetTheory.Internal

/-! ## 集合隶属结构中的统一司寇伦见证公式

载体 X 的结构码在公式内部唯一确定，因此可用同一条原公式表达全部内部公式码
的存在见证；不对整个背景宇宙假设可定义真值。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Smem_d (c X R : M.Domain) : Prop := Smdl_d I c X R ∧
  ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y

def smem_m {n} (c X R : Term n) : Formula 1 n := .conj (smdl_m (𝒞 := 𝒞) c X R)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
    (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken) (.mem (.bound 1) .newest))))))
derive_free_closed smem_m

theorem smem_sat_l {n} (ρ : Env M n) (c X R : Term n) :
    Formula.satisfies ρ (smem_m (𝒞 := 𝒞) c X R) ↔ Smem_d I (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [smem_m, Smem_d, Formula.satisfies_conj_iff, smdl_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem smem_unique_l (hE : Extensional M) {c X R d S} (h : Smem_d I c X R) (k : Smem_d I d X S) :
    c = d ∧ R = S := by
  have he := h.1.2.2.1.eq_of_pairMember_iff hE k.1.2.2.1 (fun x y => (h.2 x y).trans (k.2 x y).symm)
  subst S
  exact ⟨I.unique h.1.1 k.1.1, rfl⟩

def Ssk_mem_d (ω X u a i s x : M.Domain) : Prop := ∃ c R,
  Smem_d I c X R ∧ M.mem x X ∧ Ssk_wit_d I ω c X u a i s x

def ssk_mem_m {d} (ω X u a i s x : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (smem_m (𝒞 := 𝒞) (.bound 1) X.weaken.weaken .newest)
    (.conj (.mem x.weaken.weaken X.weaken.weaken)
      (ssk_wit_m (𝒞 := 𝒞) ω.weaken.weaken (.bound 1) X.weaken.weaken u.weaken.weaken
        a.weaken.weaken i.weaken.weaken s.weaken.weaken x.weaken.weaken))))
derive_free_closed ssk_mem_m

theorem ssk_mem_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X u a i s x : Term d) :
    Formula.satisfies ρ (ssk_mem_m (𝒞 := 𝒞) ω X u a i s x) ↔
      Ssk_mem_d I (ω.eval ρ) (X.eval ρ) (u.eval ρ) (a.eval ρ) (i.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ssk_mem_m, Ssk_mem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l I, Formula.satisfies_mem_iff, ssk_wit_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem ssk_mem_decode_l (hE : Extensional M) {ω X u a i s x c R} (h : Smem_d I c X R) :
    Ssk_mem_d I ω X u a i s x ↔ M.mem x X ∧ Ssk_wit_d I ω c X u a i s x := by
  constructor
  · rintro ⟨d, S, hd, hx, ht⟩
    exact ⟨hx, (smem_unique_l I hE hd h).1 ▸ ht⟩
  · exact fun hx => ⟨c, R, h, hx⟩

/-- 参数依次为内部 ω、载体、基点、公式码、变量号和有限赋值图。 -/
def ssk_mem_s (𝒞 : OrderedPairConvention) : UnarySchema 6 := {
  body := ssk_mem_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

end YesMetaZFC.SetTheory.Internal

/-! ## 完整内部初等结构的 Σ₁ 子结构实例

复用现有内部公式编译和满足关系，真实结构码的隶属解释与普通子类型模型
通过成员满的恒等映射对应。不把内部初等性改成未实现的额外接口字段。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 两种源解码具有同一载体和同一隶属关系，故全部原公式一致。 -/
theorem smem_formula_l {c X R : M.Domain} (h : Smem_d I c X R)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {n} (φ : Formula 1 n)
    (ρ : Env (rt_model_l X hn) n) : Formula.satisfies ρ φ ↔
      Formula.satisfies (⟨ρ.bound, ρ.free⟩ : Env (smdl_structure_l I (R := R) h.1.2.1) n) φ := by
  have eq : (fun x y : {a // M.mem a X} => M.PairMember I x.val y.val R) =
      (fun x y : {a // M.mem a X} => M.mem x.val y.val) :=
    funext fun x => funext fun y => propext (smem_member_l I h.1 h.2 x y)
  rcases ρ with ⟨bound, free⟩
  exact Iff.of_eq (congrArg (fun r : {a // M.mem a X} → {a // M.mem a X} → Prop =>
    Formula.satisfies (ℳ := ⟨{a // M.mem a X}, hn, r⟩) ⟨bound, free⟩ φ) eq).symm

theorem smem_delta_image_l {c X R : M.Domain} (hm : Smem_d I c X R) (hX : M.TransitiveSet X)
    {n} {φ : Formula 1 n} (hd : φ.IsDelta0) (ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l Subtype.val ρ) φ := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  let ne : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  exact (smem_formula_l I hm ne φ ⟨ρ.bound, ρ.free⟩).symm.trans (rt_model_delta_l hX ne hd _)

theorem smem_sub_l {c d U R X S : M.Domain} (h : Smem_d I c U R) (s : Ssub_d I c d U R X S) : Smem_d I d X S := by
  refine ⟨s.target, fun x y => (s.relation x y).trans ?_⟩
  exact ⟨fun ⟨hx, hy, hxy⟩ => ⟨hx, hy, ((h.2 x y).mp hxy).2.2⟩,
    fun ⟨hx, hy, hxy⟩ => ⟨hx, hy, (h.2 x y).mpr ⟨s.subset x hx, s.subset y hy, hxy⟩⟩⟩

theorem selem_sigma1_sub_l (hZF : M.Models ZF) {ω c d U R X S : M.Domain} (hω : M.IsOmega ω)
    (h : Smem_d I c U R) (s : Ssub_d I c d U R X S) (he : Selem_d I ω c d) : S1_sub_d X U := by
  have small := smem_sub_l I h s
  refine ⟨s.subset, s.target.2.1.elim (fun x hx => ⟨⟨x, hx⟩⟩), ?_⟩
  intro hX hU n φ ρ η same
  let ρ' : Env (smdl_structure_l I (R := S) s.target.2.1) n := ⟨ρ.bound, ρ.free⟩
  let η' : Env (smdl_structure_l I (R := R) s.source.2.1) n := ⟨η.bound, η.free⟩
  have hx : (∃ x, φ.toUnarySchema.denote ρ x) ↔ ∃ x, φ.toUnarySchema.denote ρ' x :=
    exists_congr fun x => smem_formula_l I small hX φ.body (ρ.push x)
  have hu : (∃ x, φ.toUnarySchema.denote η x) ↔ ∃ x, φ.toUnarySchema.denote η' x :=
    exists_congr fun x => smem_formula_l I h hU φ.body (η.push x)
  have eq := selem_source_l I hZF hω s he (.existsE φ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) η' ρ' (fun i => (same i).symm)
  exact hx.trans (((Formula.satisfies_exists_iff _ _).symm.trans
    (eq.symm.trans (Formula.satisfies_exists_iff _ _))).trans hu.symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 内部可数初等 H(χ) 子模型的原公式

载体、真值码与初等性均使用已实现的内部模型编码。这个有界环境的性质可
作为一条原公式用于力迫和内部递归，不以元层的泛型量化替代对象理论证书。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Hsub_d (ω χ X N : M.Domain) : Prop := M.IsOmega ω ∧ M.IsRegularCardinal I χ ∧ M.mem ω χ ∧
  H_d I χ X ∧ M.CardinalLessOrEqual I N ω ∧
    ∃ c R d S, Smem_d I c X R ∧ Ssub_d I c d X R N S ∧ Selem_d I ω c d

def hsub_m {n} (ω χ X N : Term n) : Formula 1 n :=
  .conj (Formula.isOmega ω) (.conj (Formula.isRegularCardinal 𝒞 χ) (.conj (.mem ω χ)
    (.conj (h_m (𝒞 := 𝒞) χ X) (.conj (Formula.cardinalLessOrEqual 𝒞 N ω)
      (.existsE (.existsE (.existsE (.existsE
        (.conj (smem_m (𝒞 := 𝒞) (.bound 3) X.weaken.weaken.weaken.weaken (.bound 2))
        (.conj (ssub_m (𝒞 := 𝒞) (.bound 3) (.bound 1) X.weaken.weaken.weaken.weaken (.bound 2)
          N.weaken.weaken.weaken.weaken .newest)
          (selem_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))))))))))))
derive_free_closed hsub_m

theorem hsub_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω χ X N : Term n) :
    Formula.satisfies ρ (hsub_m (𝒞 := 𝒞) ω χ X N) ↔ Hsub_d I (ω.eval ρ) (χ.eval ρ) (X.eval ρ) (N.eval ρ) := by
  simp only [hsub_m, Hsub_d, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isRegularCardinal_iff I hE, Formula.satisfies_mem_iff, h_sat_l I hE,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, Formula.satisfies_exists_iff,
    smem_sat_l I, ssub_sat_l I, selem_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
