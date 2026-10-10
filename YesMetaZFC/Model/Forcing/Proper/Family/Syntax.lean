import YesMetaZFC.Model.Forcing.Proper.Family.Basic
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 全阶段 H(χ) 提升的内部力迫证书

每个成员阶段、每个主条件及其规范 N[G] 名称都由对象量词约束。
证书正文只含原公式与实际名称力迫，可直接进入内部递归模式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u

def hsub_body_m : Formula 1 4 := hsub_m (𝒞 := kpair_convention_l) (.bound 3) (.bound 2) (.bound 1) .newest
@[simp] theorem hsub_body_closed_l : hsub_body_m.FreeClosed := hsub_m_freeClosed _ _ _ _ rfl rfl rfl rfl

def hsub_env_l {M : SetTheory.Structure.{u}} (w v ν μ : M.Domain) : Env M 4 :=
  (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push v).push ν).push μ

def hsub_force_m {n} (B R q w v ν μ : Term n) : Formula 1 n :=
  force_at_m hsub_body_m (Fin.cases μ (Fin.cases ν (Fin.cases v (fun _ => w)))) B R B q

@[simp] theorem hsub_force_closed_l {n} (B R q w v ν μ : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hq : q.freeSupport = [])
    (hw : w.freeSupport = []) (hv : v.freeSupport = []) (hν : ν.freeSupport = []) (hμ : μ.freeSupport = []) :
    (hsub_force_m B R q w v ν μ).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ hsub_body_closed_l
    (Fin.cases hμ (Fin.cases hν (Fin.cases hv (fun _ => hw)))) hB hR hB hq

theorem hsub_force_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R q w v ν μ : Term n) : Formula.satisfies ρ (hsub_force_m B R q w v ν μ) ↔
      Forces_d M (B.eval ρ) (R.eval ρ) (B.eval ρ) hsub_body_m
        (hsub_env_l (w.eval ρ) (v.eval ρ) (ν.eval ρ) (μ.eval ρ)) (q.eval ρ) :=
  (force_at_sat_l _ _ _ _ _ _ _).trans (forces_env_l hE _ hsub_body_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) _)

def Hlift_d (M : SetTheory.Structure.{u}) (ω δ F G b χ X N w v : M.Domain) : Prop :=
  Check_d M b ω w ∧ Check_d M b χ v ∧
  ∀ i B R q ν μ, M.mem i δ → M.mem i N → Entry_d M i B F → Entry_d M i R G →
    Cond_order_d M B R B → M.mem b B → Mstr_d M B R B N q → Entry_d M q b R →
    Ng_name_d M B X ν → Ng_name_d M B N μ →
      Forces_d M B R B hsub_body_m (hsub_env_l w v ν μ) q

def hlift_m {n} (ω δ F G b χ X N w v : Term n) : Formula 1 n :=
  .conj (check_m b ω w) (.conj (check_m b χ v)
    (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
      (.imp (.mem (.bound 5) δ.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (.mem (.bound 5) N.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 5) (.bound 4) F.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 5) (.bound 3) G.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (cond_order_m (.bound 4) (.bound 3) (.bound 4))
      (.imp (.mem b.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4))
      (.imp (mstr_m (.bound 4) (.bound 3) (.bound 4) N.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2))
      (.imp (entry_m (.bound 2) b.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3))
      (.imp (ng_name_m (.bound 4) X.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1))
      (.imp (ng_name_m (.bound 4) N.weaken.weaken.weaken.weaken.weaken.weaken .newest)
        (hsub_force_m (.bound 4) (.bound 3) (.bound 2) w.weaken.weaken.weaken.weaken.weaken.weaken
          v.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest))))))))))))))))))
derive_free_closed hlift_m

theorem hlift_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (ω δ F G b χ X N w v : Term n) : Formula.satisfies ρ (hlift_m ω δ F G b χ X N w v) ↔
      Hlift_d M (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (χ.eval ρ)
        (X.eval ρ) (N.eval ρ) (w.eval ρ) (v.eval ρ) := by
  simp only [hlift_m, Hlift_d, Formula.satisfies_conj_iff, check_sat_l M hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    entry_sat_l M hE, cond_order_sat_l hE, mstr_sat_l M hE, ng_name_sat_l M hE,
    hsub_force_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
