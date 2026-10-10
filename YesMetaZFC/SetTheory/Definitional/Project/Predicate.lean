import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy

/-! # 有限参数原公式的统一实例化

一元、二元 schema 通过显式项代入取得原公式；绑定参数与自由闭合性在本层
统一核验，供可定义类、秩界和力迫谓词共同使用。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project
universe u
variable (M : Structure.{u})

def pred_m {k n} (φ : UnarySchema k) (e : Fin k → Term n) (p : Term n) : Formula 1 n :=
  φ.body.bind (Fin.cases p e)

@[simp] theorem pred_m_freeClosed {k n} (φ : UnarySchema k) (e : Fin k → Term n) (p : Term n)
    (he : ∀ i, (e i).freeSupport = []) (hp : p.freeSupport = []) : (pred_m φ e p).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ φ.body).mpr φ.freeClosed
  exact Fin.cases hp he

theorem pred_sat_l {k n} (φ : UnarySchema k) (ρ : Env M n) (e : Fin k → Term n) (p : Term n) :
    Formula.satisfies ρ (pred_m φ e p) ↔
      φ.denote (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k) (p.eval ρ) := by
  rw [pred_m, Formula.satisfies_bind]
  have h : Definitional.Env.substitute ρ (Fin.cases p e) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k).push (p.eval ρ) := by
    rw [Env.mk.injEq]
    constructor
    · funext i; exact Fin.cases rfl (fun _ => rfl) i
    · rfl
  rw [h]
  rfl

section
variable {M}

def binary_pred_m {k n} (φ : BinarySchema k) (e : Fin k → Term n) (a b : Term n) : Formula 1 n :=
  pred_m ({ body := φ.body, freeClosed := φ.freeClosed } : UnarySchema (k + 1)) (Fin.cases a e) b

@[simp] theorem binary_pred_closed_l {k n} (φ : BinarySchema k) (e : Fin k → Term n) (a b : Term n)
    (he : ∀ i, (e i).freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (binary_pred_m φ e a b).FreeClosed := pred_m_freeClosed _ _ _ (Fin.cases ha he) hb

theorem binary_pred_sat_l {k n} (φ : BinarySchema k) (ρ : Env M n) (e : Fin k → Term n) (a b : Term n) :
    Formula.satisfies ρ (binary_pred_m φ e a b) ↔
      φ.denote (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k) (a.eval ρ) (b.eval ρ) := by
  rw [binary_pred_m, pred_sat_l]
  have he : (⟨fun i => (Fin.cases a e i : Term n).eval ρ, ρ.free⟩ : Env M (k+1)) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k).push (a.eval ρ) := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
  rw [he]
  rfl

end

end YesMetaZFC.SetTheory.Definitional.Project
