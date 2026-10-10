import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttempt
import YesMetaZFC.Model.SetTheory.Internal.FiniteEvaluationSyntax

/-! # 尝试节点的原公式

先把一致性、指定限制和双边有限真值检验写成 Δ₀ 公式。
无界量词只选择程序与实际有限真值证书，便于在传递源内逐项读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def at_coherent_m {d} (n A B e p : Term d) : Formula 1 d :=
  Formula.forallMem n (Formula.forallMem n.weaken (.iff
    (Formula.existsMem A.weaken.weaken (.conj (rd_entry0_m (.bound 2) .newest e.weaken.weaken.weaken)
      (rd_entry0_m (.bound 1) .newest e.weaken.weaken.weaken)))
    (Formula.existsMem B.weaken.weaken (.conj (rd_entry0_m (.bound 2) .newest p.weaken.weaken.weaken)
      (rd_entry0_m (.bound 1) .newest p.weaken.weaken.weaken)))))
derive_free_closed at_coherent_m

theorem at_coherent_delta_l {d} (n A B e p : Term d) : (at_coherent_m n A B e p).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem at_coherent_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n A B e p : Term d) :
    Formula.satisfies ρ (at_coherent_m n A B e p) ↔
      At_coherent_d (n.eval ρ) (A.eval ρ) (B.eval ρ) (e.eval ρ) (p.eval ρ) := by
  simp only [at_coherent_m, At_coherent_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

def at_prescribed_m {d} (n A B e τ p : Term d) : Formula 1 d :=
  Formula.forallMem n (Formula.forallMem A.weaken (Formula.forallMem B.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) (.bound 1) e.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 1) .newest τ.weaken.weaken.weaken)
        (rd_entry0_m (.bound 2) .newest p.weaken.weaken.weaken)))))
derive_free_closed at_prescribed_m

theorem at_prescribed_delta_l {d} (n A B e τ p : Term d) : (at_prescribed_m n A B e τ p).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem at_prescribed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n A B e τ p : Term d) :
    Formula.satisfies ρ (at_prescribed_m n A B e τ p) ↔
      At_prescribed_d (n.eval ρ) (A.eval ρ) (B.eval ρ) (e.eval ρ) (τ.eval ρ) (p.eval ρ) := by
  simp only [at_prescribed_m, At_prescribed_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def At_test_d (ω A B e n p Q b l E D C H C' H' : M.Domain) : Prop :=
  ∀ r, M.mem r l → ∀ q, M.mem q Q → ∀ s, M.mem s E → ∀ t, M.mem t D →
    Fn0_d b n q → Cp0_d b ω A q e s → Cp0_d b n B q p t →
      (Fv_at_d C H r s ↔ Fv_at_d C' H' r t)

def at_test_m {d} (ω A B e n p Q b l E D C H C' H' : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  Formula.forallMem l (Formula.forallMem Q.weaken (Formula.forallMem E.weaken.weaken
    (Formula.forallMem D.weaken.weaken.weaken (.imp (fn0_m (w b) (w n) (.bound 2))
      (.imp (cp0_m (w b) (w ω) (w A) (.bound 2) (w e) (.bound 1))
        (.imp (cp0_m (w b) (w n) (w B) (.bound 2) (w p) .newest)
          (.iff (fv_at_m (w C) (w H) (.bound 3) (.bound 1)) (fv_at_m (w C') (w H') (.bound 3) .newest))))))))
derive_free_closed at_test_m

theorem at_test_delta_l {d} (ω A B e n p Q b l E D C H C' H' : Term d) :
    (at_test_m ω A B e n p Q b l E D C H C' H').IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (fn0_delta_l ..)
    (.imp (cp0_delta_l ..) (.imp (cp0_delta_l ..) (.iff (fv_at_delta_l ..) (fv_at_delta_l ..))))))))

theorem at_test_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B e n p Q b l E D C H C' H' : Term d) :
    Formula.satisfies ρ (at_test_m ω A B e n p Q b l E D C H C' H') ↔ At_test_d
      (ω.eval ρ) (A.eval ρ) (B.eval ρ) (e.eval ρ) (n.eval ρ) (p.eval ρ) (Q.eval ρ) (b.eval ρ)
      (l.eval ρ) (E.eval ρ) (D.eval ρ) (C.eval ρ) (H.eval ρ) (C'.eval ρ) (H'.eval ρ) := by
  simp only [at_test_m, At_test_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, cp0_sat_l hE, Formula.satisfies_iff_iff, fv_at_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

def At_cert_d (hKP : M.Models KP) (ω A R B S e n p Q J K b l L F E D C H C' H' : M.Domain) : Prop :=
  Fv_space_d b A J E ∧ Fv_space_d b B K D ∧ Fv_eval_d hKP b A R E l L F C H ∧
    Fv_eval_d hKP b B S D l L F C' H' ∧ At_test_d ω A B e n p Q b l E D C H C' H'

def at_cert_m {d} (ω A R B S e n p Q J K b l L F E D C H C' H' : Term d) : Formula 1 d :=
  .conj (fv_space_m b A J E) (.conj (fv_space_m b B K D) (.conj (fv_eval_m b A R E l L F C H)
    (.conj (fv_eval_m b B S D l L F C' H') (at_test_m ω A B e n p Q b l E D C H C' H'))))
derive_free_closed at_cert_m

theorem at_cert_delta_l {d} (ω A R B S e n p Q J K b l L F E D C H C' H' : Term d) :
    (at_cert_m ω A R B S e n p Q J K b l L F E D C H C' H').IsDelta0 :=
  .conj (fv_space_delta_l ..) (.conj (fv_space_delta_l ..) (.conj (fv_eval_delta_l ..)
    (.conj (fv_eval_delta_l ..) (at_test_delta_l ..))))

theorem at_cert_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω A R B S e n p Q J K b l L F E D C H C' H' : Term d) :
    Formula.satisfies ρ (at_cert_m ω A R B S e n p Q J K b l L F E D C H C' H') ↔ At_cert_d hKP
      (ω.eval ρ) (A.eval ρ) (R.eval ρ) (B.eval ρ) (S.eval ρ) (e.eval ρ) (n.eval ρ) (p.eval ρ)
      (Q.eval ρ) (J.eval ρ) (K.eval ρ) (b.eval ρ) (l.eval ρ) (L.eval ρ) (F.eval ρ)
      (E.eval ρ) (D.eval ρ) (C.eval ρ) (H.eval ρ) (C'.eval ρ) (H'.eval ρ) := by
  simp only [at_cert_m, At_cert_d, Formula.satisfies_conj_iff, fv_space_sat_l hKP.1,
    fv_eval_sat_l hKP, at_test_sat_l hKP.1]

/-- 六个见证都是可检验的集合与函数图。 -/
def at_witness_m {d} (ω A R B S e n p Q J K b l L F : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (at_cert_m (w ω) (w A) (w R) (w B) (w S) (w e) (w n) (w p) (w Q) (w J) (w K)
      (w b) (w l) (w L) (w F) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))
derive_free_closed at_witness_m

def at_elementary_m {d} (ω A R B S e n p Q J K : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  .forallE (.forallE (.forallE (.forallE (.imp (fb_program_m (w ω) (.bound 3) (.bound 2) (.bound 1) .newest)
    (at_witness_m (w ω) (w A) (w R) (w B) (w S) (w e) (w n) (w p) (w Q) (w J) (w K)
      (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed at_elementary_m

def at_node_m {d} (ω A R B S e τ p Q J K : Term d) : Formula 1 d :=
  Formula.existsMem ω (.conj (fn0_m .newest B.weaken p.weaken)
    (.conj (at_coherent_m .newest A.weaken B.weaken e.weaken p.weaken)
      (.conj (at_prescribed_m .newest A.weaken B.weaken e.weaken τ.weaken p.weaken)
        (at_elementary_m ω.weaken A.weaken R.weaken B.weaken S.weaken e.weaken .newest p.weaken Q.weaken J.weaken K.weaken))))
derive_free_closed at_node_m

end YesMetaZFC.SetTheory.Internal
