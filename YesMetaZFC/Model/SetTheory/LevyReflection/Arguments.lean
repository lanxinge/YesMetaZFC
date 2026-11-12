import YesMetaZFC.Model.SetTheory.LevyReflection.Relativization

/-! # 相对化公式只依赖实际载体和实参

先对原公式证明参数替换，再用于大名字公式，避免展开全部力迫语法来检查定义相等。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem lr_rel_arguments_l {n d k} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env M d) (η : Env M k) (X : Term d) (Y : Term k)
    (e : Fin n → Term d) (f : Fin n → Term k)
    (sameX : X.eval ρ = Y.eval η) (same : ∀ i, (e i).eval ρ = (f i).eval η) :
    Formula.satisfies ρ (lr_rel_m φ X e) ↔ Formula.satisfies η (lr_rel_m φ Y f) := by
  have term {n d k} (ρ : Env M d) (η : Env M k) (e : Fin n → Term d) (f : Fin n → Term k)
      (same : ∀ i, (e i).eval ρ = (f i).eval η) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind e).eval ρ = (t.bind f).eval η := by
    cases t with
    | free _ => simp at ht
    | bound i => exact same i
  induction φ generalizing d k with
  | falsum | truth => simp only [lr_rel_m,Formula.satisfies_falsum_iff,Formula.satisfies_truth_iff]
  | mem s t =>
    simp only [lr_rel_m,Formula.satisfies_mem_iff,term ρ η e f same s closed.1,term ρ η e f same t closed.2]
  | atom r hr ts =>
    cases r <;> simp only [lr_rel_m,Formula.satisfies_atom_extensionalEq_iff,Formula.satisfies_atom_subset_iff,
      Definitional.TermVector.get_bind,term ρ η e f same (ts 0) (closed 0),term ρ η e f same (ts 1) (closed 1)]
  | neg φ ih => exact not_congr (ih closed ρ η X Y e f sameX same)
  | conj φ ψ ih jh => exact and_congr (ih closed.1 ρ η X Y e f sameX same) (jh closed.2 ρ η X Y e f sameX same)
  | disj φ ψ ih jh => exact or_congr (ih closed.1 ρ η X Y e f sameX same) (jh closed.2 ρ η X Y e f sameX same)
  | imp φ ψ ih jh => exact imp_congr (ih closed.1 ρ η X Y e f sameX same) (jh closed.2 ρ η X Y e f sameX same)
  | iff φ ψ ih jh => exact iff_congr (ih closed.1 ρ η X Y e f sameX same) (jh closed.2 ρ η X Y e f sameX same)
  | existsE φ ih | forallE φ ih =>
    have body x := ih closed (ρ.push x) (η.push x) X.weaken Y.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (Fin.cases .newest (fun i => (f i).weaken))
      (by simpa using sameX) (Fin.cases rfl (fun i => by simpa using same i))
    first
    | simp only [lr_rel_m,Formula.satisfies_existsMem_iff,sameX]
      exact exists_congr (fun x => and_congr_right (fun _ => body x))
    | simp only [lr_rel_m,Formula.satisfies_forallMem_iff,sameX]
      exact forall_congr' (fun x => imp_congr_right (fun _ => body x))

end YesMetaZFC.SetTheory
