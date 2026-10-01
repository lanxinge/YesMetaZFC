import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Reflection
import YesMetaZFC.Model.SetTheory.LevyReflection.Relativization

/-! # ZF 背景下 J 的全分离

对给定公式的量词子公式及反例同时反射。相对化后的全部量词有界，故原来的
KP 分离即可构造目标集合；反射只用来证明这个集合满足原公式的精确规格。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem jl_rel_delta_l {n d} (φ : Formula 1 n) (U : Term d) (e : Fin n → Term d) :
    (lr_rel_m φ U e).IsDelta0 := by
  induction φ generalizing d with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem s t => exact .mem _ _
  | atom r hr ts => exact .atom _ _ _
  | neg φ ih => exact .neg (ih U e)
  | conj φ ψ ih jh => exact .conj (ih U e) (jh U e)
  | disj φ ψ ih jh => exact .disj (ih U e) (jh U e)
  | imp φ ψ ih jh => exact .imp (ih U e) (jh U e)
  | iff φ ψ ih jh => exact .iff (ih U e) (jh U e)
  | forallE φ ih => exact .forallMem _ (ih _ _)
  | existsE φ ih => exact .existsMem _ (ih _ _)

theorem l_model_full_separation_l (hZF : M.Models ZF) {n} (φ : UnarySchema n)
    (ρ : Env (l_model_l (ZF.models_kpi_l hZF)) n)
    (X : (l_model_l (ZF.models_kpi_l hZF)).Domain) :
    ∃ Y : (l_model_l (ZF.models_kpi_l hZF)).Domain, ∀ x,
      (l_model_l (ZF.models_kpi_l hZF)).mem x Y ↔
        (l_model_l (ZF.models_kpi_l hZF)).mem x X ∧ φ.denote ρ x := by
  let hM := ZF.models_kpi_l hZF
  let N := l_model_l hM
  obtain ⟨b, S, hb, hS⟩ := l_finite_bound_l hM (fun i => ((ρ.push X).bound i).val)
    (fun i => ((ρ.push X).bound i).property)
  let A : N.Domain := ⟨S, l_layer_l hM hb⟩
  obtain ⟨a, U, ha, hAU, hc⟩ := jl_closed_layer_l hZF (lr_queries_l φ.body φ.freeClosed) A
  have ht : N.TransitiveSet U := fun x hx y hy => jh_value_transitive_l hM ha.2 x.val hx y.val hy
  have hX : N.mem X U := jh_value_transitive_l hM ha.2 S hAU X.val (hS 0)
  have hρ i : N.mem (ρ.bound i) U := jh_value_transitive_l hM ha.2 S hAU _ (hS i.succ)
  let e : Fin (n + 1) → Term (n + 2) := Fin.cases .newest (fun i => .bound ⟨i.val + 2, by omega⟩)
  let ψ : Delta0UnarySchema (n + 1) := {
    body := lr_rel_m φ.body (.bound 1) e
    freeClosed := lr_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))
    delta0 := jl_rel_delta_l .. }
  have tr x (hx : N.mem x X) : φ.denote ρ x ↔ ψ.toUnarySchema.denote (ρ.push U) x :=
    lr_reflect_core_l φ.body φ.freeClosed hc (ρ.push x) ((ρ.push U).push x) (.bound 1) e
      rfl (Fin.cases rfl (fun _ => rfl)) (Fin.cases (ht X hX x hx) hρ)
  obtain ⟨Y, hy⟩ := l_model_separation_l hM ψ (ρ.push U) X
  exact ⟨Y, fun x => (hy x).trans (and_congr_right fun hx => (tr x hx).symm)⟩

end YesMetaZFC.SetTheory.InnerModel
