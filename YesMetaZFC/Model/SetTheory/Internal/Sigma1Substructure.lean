import YesMetaZFC.Model.SetTheory.Internal.SourceElementary
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.Model.SetTheory.Sigma1Substructure

/-! # 完整内部初等结构的 Σ₁ 子结构实例

复用现有内部公式编译和满足关系，真实结构码的隶属解释与普通子类型模型
通过成员满的恒等映射对应。不把内部初等性改成未实现的额外接口字段。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smem_delta_l {c X R : M.Domain} (h : Smem_d I c X R)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {n} {φ : Formula 1 n} (hφ : φ.IsDelta0)
    (ρ : Env (rt_model_l X hn) n) : Formula.satisfies ρ φ ↔
      Formula.satisfies (⟨ρ.bound, ρ.free⟩ : Env (smdl_structure_l I (R := R) h.1.2.1) n) φ := by
  exact delta0_image_l (M := rt_model_l X hn) (N := smdl_structure_l I (R := R) h.1.2.1)
    (fun x => x) (fun _ _ he => he) (fun a y => (smem_member_l I h.1 h.2 y a).trans
      ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨x, hx, he⟩ => he ▸ hx⟩) hφ ρ

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
    exists_congr fun x => smem_delta_l I small hX φ.delta0 (ρ.push x)
  have hu : (∃ x, φ.toUnarySchema.denote η x) ↔ ∃ x, φ.toUnarySchema.denote η' x :=
    exists_congr fun x => smem_delta_l I h hU φ.delta0 (η.push x)
  have eq := selem_source_l I hZF hω s he (.existsE φ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) η' ρ' (fun i => (same i).symm)
  exact hx.trans (((Formula.satisfies_exists_iff _ _).symm.trans
    (eq.symm.trans (Formula.satisfies_exists_iff _ _))).trans hu.symm)

end YesMetaZFC.SetTheory.Internal
