import YesMetaZFC.Model.Boolean.Soundness
import YesMetaZFC.Model.FirstOrder.Morphism

/-! # 命题布尔代数与原生语义的对应

原结构只重解释真值，项和环境沿恒等载体映射保持。全部公式及理论模型性恢复原接口。
-/

namespace YesMetaZFC.Model.Boolean
open Logic Logic.FirstOrder
universe u v w x y

theorem prop_sup_iff {ι : Sort y} (p : ι → Prop) : prop_algebra.iSup p ↔ ∃ i, p i :=
  ⟨(prop_algebra.iSup_le_iff p _).mpr (fun i h => ⟨i, h⟩), fun ⟨i, h⟩ => prop_algebra.le_iSup p i h⟩

theorem prop_inf_iff {ι : Sort y} (p : ι → Prop) : prop_algebra.iInf p ↔ ∀ i, p i :=
  ⟨fun h i => prop_algebra.iInf_le p i h,
    (prop_algebra.le_iInf_iff p _).mpr (fun i h => h i)⟩

theorem prop_join_iff (p q : Prop) : prop_algebra.join p q ↔ p ∨ q := by
  classical
  change (¬ (¬ p ∧ ¬ q)) ↔ p ∨ q
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr (Classical.byContradiction (fun hq => h ⟨hp, hq⟩))
  · rintro (h | h) ⟨hp, hq⟩
    · exact hp h
    · exact hq h

variable {σ : Signature.{u, v, w}} (ℳ : Structure.{u, v, w, x} σ)

def native_map : Fn_map ℳ (BV_str.top_structure prop_algebra.toBA_alg (native_str ℳ)) where
  map _ := id
  function_eq a ts := congrArg (ℳ.funcInterp a) (Values.map_id ts).symm

attribute [local implicit_reducible] native_str native_map

theorem native_value {b f} (φ : Formula σ b f) (ρ : Env ℳ b f) :
    BV_str.value prop_algebra (native_str ℳ) φ (ρ.map (native_map ℳ).map) ↔ φ.satisfies ρ := by
  induction φ with
  | falsum => rfl
  | truth => exact ⟨fun _ => trivial, fun _ => id⟩
  | equal t t' =>
    rw [BV_str.value_equal, ← (native_map ℳ).term_eval_eq ρ t, ← (native_map ℳ).term_eval_eq ρ t']
    rfl
  | rel r ts =>
    rw [BV_str.value_rel, ← (native_map ℳ).arguments_eval_eq ρ ts]
    change ℳ.relInterp r ((ts.eval ρ).map (fun _ a => a)) ↔ ℳ.relInterp r (ts.eval ρ)
    rw [Values.map_id]
  | neg φ ih => exact not_congr (ih ρ)
  | conj φ ψ ih ik => exact and_congr (ih ρ) (ik ρ)
  | disj φ ψ ih ik => exact (prop_join_iff _ _).trans (or_congr (ih ρ) (ik ρ))
  | imp φ ψ ih ik => exact imp_congr (ih ρ) (ik ρ)
  | iff φ ψ ih ik =>
    exact (show ((_ → _) ∧ (_ → _)) ↔ (_ ↔ _) from
      ⟨fun ⟨h, k⟩ => ⟨h, k⟩, fun h => ⟨h.mp, h.mpr⟩⟩).trans (iff_congr (ih ρ) (ik ρ))
  | forallE s φ ih =>
    rw [BV_str.value_all, prop_inf_iff]
    exact forall_congr' (fun a => by simpa only [Env.map_pushBound, native_map, id] using ih (ρ.pushBound a))
  | existsE s φ ih =>
    rw [BV_str.value_ex, prop_sup_iff]
    exact exists_congr (fun a => by simpa only [Env.map_pushBound, native_map, id] using ih (ρ.pushBound a))

theorem native_models (T : Theory σ) :
    (BV_str.model prop_algebra (native_str ℳ)).models T ↔ Theory.Models ℳ T := by
  constructor
  · intro h φ hφ
    exact (native_value ℳ φ Env.empty).mp (h φ hφ _ id)
  · intro h φ hφ ρ _
    rw [Env.empty_unique ρ]
    simpa only [Env.map_empty] using (native_value ℳ φ Env.empty).mpr (h φ hφ)

end YesMetaZFC.Model.Boolean
