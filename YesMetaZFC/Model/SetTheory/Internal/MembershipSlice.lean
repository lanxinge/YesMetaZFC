import YesMetaZFC.Model.SetTheory.Relations.RecordImage

/-! # 给定隶属模型切片的逐项解码

只有实际隶属结构才使用此识别。反射层包含于给定载体已足够；不要求整个
载体传递。原关系后继直接使用原生切片，无须调用此识别。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
  {c X R : M.Domain} (model : Smem_d I c X R)
local notation "X₀" => smdl_structure_l I (R := R) (And.left (And.right (And.left model)))

theorem Smem_d.slice_transitive_l (C : (X₀).Domain) (trans : M.TransitiveSet C.val) :
    (X₀).TransitiveSet C := by
  intro x hx y hy
  exact (model.2 y.val C.val).mpr ⟨y.property, C.property,
    trans x.val ((model.2 x.val C.val).mp hx).2.2 y.val ((model.2 y.val x.val).mp hy).2.2⟩

/-- 删除双重子类型标签；对象码和成员关系都保持原值。 -/
def Smem_d.slice_env_d (C : (X₀).Domain)
    (nc : Nonempty {x : (X₀).Domain // (X₀).mem x C})
    (nv : Nonempty {x // M.mem x C.val}) {n} (ρ : Env (rt_model_l C nc) n) : Env (rt_model_l C.val nv) n :=
  image_env_l (M := rt_model_l C nc) (N := rt_model_l C.val nv)
    (fun x => ⟨x.val.val, ((model.2 x.val.val C.val).mp x.property).2.2⟩) ρ

theorem Smem_d.slice_formula_l (C : (X₀).Domain) (inside : M.MemberSubset C.val X)
    (nc : Nonempty {x : (X₀).Domain // (X₀).mem x C})
    (nv : Nonempty {x // M.mem x C.val}) {n} (φ : Formula 1 n) (ρ : Env (rt_model_l C nc) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (model.slice_env_d I C nc nv ρ) φ := by
  let e : (rt_model_l C nc).Domain → (rt_model_l C.val nv).Domain :=
    fun x => ⟨x.val.val, ((model.2 x.val.val C.val).mp x.property).2.2⟩
  apply formula_image_l e ?_ ?_ φ ρ
  · exact fun y => ⟨⟨⟨y.val, inside y.val y.property⟩,
      (model.2 y.val C.val).mpr ⟨inside y.val y.property, C.property, y.property⟩⟩, rfl⟩
  · exact fun x y => (smem_member_l I model.1 model.2 x.val y.val)

/-- 同一个给定隶属切片中的赋值进入原模型，不改变任何坐标。 -/
def Smem_d.native_env_d (C : (X₀).Domain) (inside : M.MemberSubset C.val X)
    (nc : Nonempty {x : (X₀).Domain // (X₀).mem x C})
    (nv : Nonempty {x // M.mem x C.val}) {n} (ρ : Env (rt_model_l C.val nv) n) : Env (rt_model_l C nc) n :=
  image_env_l (M := rt_model_l C.val nv) (N := rt_model_l C nc) (fun x => ⟨⟨x.val, inside x.val x.property⟩,
    (model.2 x.val C.val).mpr ⟨inside x.val x.property, C.property, x.property⟩⟩) ρ

theorem Smem_d.native_formula_l (C : (X₀).Domain) (inside : M.MemberSubset C.val X)
    (nc : Nonempty {x : (X₀).Domain // (X₀).mem x C})
    (nv : Nonempty {x // M.mem x C.val}) {n} (φ : Formula 1 n) (ρ : Env (rt_model_l C.val nv) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (model.native_env_d I C inside nc nv ρ) φ := by
  have eq : model.slice_env_d I C nc nv (model.native_env_d I C inside nc nv ρ) = ρ := by
    cases ρ
    rfl
  have read := model.slice_formula_l I C inside nc nv φ (model.native_env_d I C inside nc nv ρ)
  rw [eq] at read
  exact read.symm

theorem Smem_d.slice_pair_l (C : (X₀).Domain) (inside : M.MemberSubset C.val X)
    (pair : ∀ a b, M.mem a C.val → M.mem b C.val → ∃ p, M.mem p C.val ∧ Pair_d M p a b) :
    ∀ a b, (X₀).mem a C → (X₀).mem b C → ∃ p, (X₀).mem p C ∧ Pair_d X₀ p a b := by
  intro a b ha hb
  obtain ⟨p, hp, spec⟩ := pair a.val b.val ((model.2 a.val C.val).mp ha).2.2
    ((model.2 b.val C.val).mp hb).2.2
  refine ⟨⟨p, inside p hp⟩, (model.2 p C.val).mpr ⟨inside p hp, C.property, hp⟩, fun z => ?_⟩
  exact (smem_member_l I model.1 model.2 z ⟨p, inside p hp⟩).trans
    ((spec z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩))

/-- 同一实际隶属切片中的元组识别只使用切片闭包。 -/
theorem Smem_d.slice_tuple_l (ext : Extensional X₀) (hE : Extensional M)
    (C : (X₀).Domain) (inside : M.MemberSubset C.val X) (trans : M.TransitiveSet C.val)
    (nc : Nonempty {x : (X₀).Domain // (X₀).mem x C})
    (nv : Nonempty {x // M.mem x C.val}) {n} (ρ : Env (rt_model_l C nc) (n+1))
    (r : (X₀).Domain) (hr : (X₀).mem r C) :
    Rf_tuple_d I X R (fun i => (ρ.bound i).val.val) r.val ↔
      Rt_tuple_d (fun i => (ρ.bound i).val.val) r.val := by
  let τ := ρ.push ⟨r, hr⟩
  let φ := rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest
  have ct := model.slice_transitive_l I C trans
  have native := (rt_tuple_sat_l (rt_model_ext_l ext ct nc) τ (fun i : Fin (n+1) => .bound i.succ) .newest).trans
    (rt_tuple_source_l ext ct nc ρ.bound ⟨r, hr⟩)
  have target := (rt_tuple_sat_l (rt_model_ext_l hE trans nv) (model.slice_env_d I C nc nv τ)
    (fun i : Fin (n+1) => .bound i.succ) .newest).trans
    (rt_tuple_source_l hE trans nv (model.slice_env_d I C nc nv ρ).bound
      ⟨r.val, ((model.2 r.val C.val).mp hr).2.2⟩)
  exact (rf_tuple_native_l I model.1.2.1 ext (fun i => (ρ.bound i).val) r).trans
    (native.symm.trans ((model.slice_formula_l I C inside nc nv φ τ).trans target))

end YesMetaZFC.SetTheory.Internal
