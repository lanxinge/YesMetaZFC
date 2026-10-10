import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctions
import YesMetaZFC.SetTheory.LargeCardinal.SupportIndex

/-! # 有界代表与共同支撑关系的有界原公式

有限函数空间在已有全部有限 κ 列中读取；节点是支撑与源内函数的有序对。
两节点之间的关系用共同有限支撑上的一个测度一集合判定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_space_d (κ K n D : M.Domain) : Prop := M.MemberSubset D K ∧
  ∀ s, M.mem s K → (M.mem s D ↔ Fn0_d n κ s)

def eb_space_m {d} (κ K n D : Term d) : Formula 1 d := .conj (Formula.subset D K)
  (Formula.forallMem K (.iff (.mem .newest D.weaken) (fn0_m n.weaken κ.weaken .newest)))
derive_free_closed eb_space_m

theorem eb_space_delta_l {d} (κ K n D : Term d) : (eb_space_m κ K n D).IsDelta0 :=
  .conj (.atom ..) (.forallMem _ (.iff (.mem ..) (fn0_delta_l ..)))

theorem eb_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ K n D : Term d) :
    Formula.satisfies ρ (eb_space_m κ K n D) ↔ Eb_space_d (κ.eval ρ) (K.eval ρ) (n.eval ρ) (D.eval ρ) := by
  simp only [eb_space_m, Eb_space_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem eb_space_iff_l (hKP : M.Models KP) {ω κ K n D : M.Domain}
    (hK : Fseq_space_d (kp_pair_l hKP) ω κ K) (hn : M.mem n ω) : Eb_space_d κ K n D ↔ Ep_space_d κ n D := by
  have mem s (hs : Fn0_d n κ s) : M.mem s K := (hK s).mpr ⟨n, hn, fn0_function_l hKP hs⟩
  exact ⟨fun h s => ⟨fun hs => (h.2 s (h.1 s hs)).mp hs, fun hs => (h.2 s (mem s hs)).mpr hs⟩,
    fun h => ⟨fun s hs => mem s ((h s).mp hs), fun s _ => h s⟩⟩

def Eb_node_d (ω κ L K B J G P u : M.Domain) : Prop := ∃ a, M.mem a J ∧ ∃ f, M.mem f G ∧
  KPair_d M u a f ∧ ∃ n, M.mem n ω ∧ ∃ D, M.mem D P ∧ Fn0_d n L a ∧ Eb_space_d κ K n D ∧ Fn0_d D B f

def eb_node_m {d} (ω κ L K B J G P u : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  Formula.existsMem J (Formula.existsMem G.weaken (.conj (kpair0_m u.weaken.weaken (.bound 1) .newest)
    (Formula.existsMem ω.weaken.weaken (Formula.existsMem P.weaken.weaken.weaken (.conj (fn0_m (.bound 1) (w L) (.bound 3))
      (.conj (eb_space_m (w κ) (w K) (.bound 1) .newest) (fn0_m .newest (w B) (.bound 2))))))))
derive_free_closed eb_node_m

theorem eb_node_delta_l {d} (ω κ L K B J G P u : Term d) : (eb_node_m ω κ L K B J G P u).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.existsMem _ (.existsMem _
    (.conj (fn0_delta_l ..) (.conj (eb_space_delta_l ..) (fn0_delta_l ..)))))))

theorem eb_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L K B J G P u : Term d) :
    Formula.satisfies ρ (eb_node_m ω κ L K B J G P u) ↔
      Eb_node_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (B.eval ρ) (J.eval ρ) (G.eval ρ) (P.eval ρ) (u.eval ρ) := by
  simp only [eb_node_m, Eb_node_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, fn0_sat_l hE, eb_space_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Eb_point_d (κ B K R m n l r t f g s : M.Domain) : Prop := ∃ u, M.mem u K ∧ ∃ v, M.mem v K ∧
  ∃ x, M.mem x B ∧ ∃ y, M.mem y B ∧ Cp0_d m l κ r s u ∧ Cp0_d n l κ t s v ∧
    Rd_entry_d u x f ∧ Rd_entry_d v y g ∧ Rd_entry_d x y R

def eb_point_m {d} (κ B K R m n l r t f g s : Term d) : Formula 1 d :=
  let w (a : Term d) := a.weaken.weaken.weaken.weaken
  Formula.existsMem K (Formula.existsMem K.weaken (Formula.existsMem B.weaken.weaken (Formula.existsMem B.weaken.weaken.weaken
    (.conj (cp0_m (w m) (w l) (w κ) (w r) (w s) (.bound 3))
      (.conj (cp0_m (w n) (w l) (w κ) (w t) (w s) (.bound 2))
        (.conj (rd_entry0_m (.bound 3) (.bound 1) (w f))
          (.conj (rd_entry0_m (.bound 2) .newest (w g)) (rd_entry0_m (.bound 1) .newest (w R)))))))))
derive_free_closed eb_point_m

theorem eb_point_delta_l {d} (κ B K R m n l r t f g s : Term d) : (eb_point_m κ B K R m n l r t f g s).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (cp0_delta_l ..)
    (.conj (cp0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))

theorem eb_point_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ B K R m n l r t f g s : Term d) :
    Formula.satisfies ρ (eb_point_m κ B K R m n l r t f g s) ↔
      Eb_point_d (κ.eval ρ) (B.eval ρ) (K.eval ρ) (R.eval ρ) (m.eval ρ) (n.eval ρ) (l.eval ρ)
        (r.eval ρ) (t.eval ρ) (f.eval ρ) (g.eval ρ) (s.eval ρ) := by
  simp only [eb_point_m, Eb_point_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    cp0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Eb_constraint_d (ω κ L B K R a f b g c E : M.Domain) : Prop :=
  ∃ m, M.mem m ω ∧ ∃ n, M.mem n ω ∧ ∃ l, M.mem l ω ∧ ∃ r, M.mem r K ∧ ∃ t, M.mem t K ∧
    Fn0_d m l r ∧ Fn0_d n l t ∧ Fn0_d l L c ∧ Cp0_d m l L r c a ∧ Cp0_d n l L t c b ∧
      ∀ s, M.mem s E → Eb_point_d κ B K R m n l r t f g s

def eb_constraint_m {d} (ω κ L B K R a f b g c E : Term d) : Formula 1 d :=
  let w (x : Term d) := x.weaken.weaken.weaken.weaken.weaken
  Formula.existsMem ω (Formula.existsMem ω.weaken (Formula.existsMem ω.weaken.weaken
    (Formula.existsMem K.weaken.weaken.weaken (Formula.existsMem K.weaken.weaken.weaken.weaken
      (.conj (fn0_m (.bound 4) (.bound 2) (.bound 1)) (.conj (fn0_m (.bound 3) (.bound 2) .newest)
        (.conj (fn0_m (.bound 2) (w L) (w c)) (.conj (cp0_m (.bound 4) (.bound 2) (w L) (.bound 1) (w c) (w a))
          (.conj (cp0_m (.bound 3) (.bound 2) (w L) .newest (w c) (w b)) (Formula.forallMem (w E)
            (eb_point_m (w κ).weaken (w B).weaken (w K).weaken (w R).weaken
              (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (w f).weaken (w g).weaken .newest)))))))))))
derive_free_closed eb_constraint_m

theorem eb_constraint_delta_l {d} (ω κ L B K R a f b g c E : Term d) : (eb_constraint_m ω κ L B K R a f b g c E).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (fn0_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (cp0_delta_l ..)
      (.conj (cp0_delta_l ..) (.forallMem _ (eb_point_delta_l ..)))))))))))

theorem eb_constraint_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L B K R a f b g c E : Term d) :
    Formula.satisfies ρ (eb_constraint_m ω κ L B K R a f b g c E) ↔
      Eb_constraint_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (B.eval ρ) (K.eval ρ) (R.eval ρ)
        (a.eval ρ) (f.eval ρ) (b.eval ρ) (g.eval ρ) (c.eval ρ) (E.eval ρ) := by
  simp only [eb_constraint_m, Eb_constraint_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_conj_iff, fn0_sat_l hE, cp0_sat_l hE, eb_point_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Eb_edge_d (ω κ L B J K V R F a f b g : M.Domain) : Prop :=
  ∃ c, M.mem c J ∧ ∃ U, M.mem U V ∧ Rd_entry_d c U F ∧ ∃ E, M.mem E U ∧ Eb_constraint_d ω κ L B K R a f b g c E

def eb_edge_m {d} (ω κ L B J K V R F a f b g : Term d) : Formula 1 d :=
  let w (x : Term d) := x.weaken.weaken.weaken
  Formula.existsMem J (Formula.existsMem V.weaken (.conj (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
    (Formula.existsMem .newest (eb_constraint_m (w ω) (w κ) (w L) (w B) (w K) (w R) (w a) (w f) (w b) (w g) (.bound 2) .newest))))
derive_free_closed eb_edge_m

theorem eb_edge_delta_l {d} (ω κ L B J K V R F a f b g : Term d) : (eb_edge_m ω κ L B J K V R F a f b g).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.existsMem _ (eb_constraint_delta_l ..))))

theorem eb_edge_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L B J K V R F a f b g : Term d) :
    Formula.satisfies ρ (eb_edge_m ω κ L B J K V R F a f b g) ↔
      Eb_edge_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) (V.eval ρ)
        (R.eval ρ) (F.eval ρ) (a.eval ρ) (f.eval ρ) (b.eval ρ) (g.eval ρ) := by
  simp only [eb_edge_m, Eb_edge_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, rd_entry0_sat_l hE, eb_constraint_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

def Eb_link_d (ω κ L B J K V R F G u v : M.Domain) : Prop := ∃ a, M.mem a J ∧ ∃ f, M.mem f G ∧
  ∃ b, M.mem b J ∧ ∃ g, M.mem g G ∧ KPair_d M u a f ∧ KPair_d M v b g ∧ Eb_edge_d ω κ L B J K V R F a f b g

def eb_link_m {d} (ω κ L B J K V R F G u v : Term d) : Formula 1 d :=
  let w (x : Term d) := x.weaken.weaken.weaken.weaken
  Formula.existsMem J (Formula.existsMem G.weaken (Formula.existsMem J.weaken.weaken (Formula.existsMem G.weaken.weaken.weaken
    (.conj (kpair0_m (w u) (.bound 3) (.bound 2)) (.conj (kpair0_m (w v) (.bound 1) .newest)
      (eb_edge_m (w ω) (w κ) (w L) (w B) (w J) (w K) (w V) (w R) (w F) (.bound 3) (.bound 2) (.bound 1) .newest))))))
derive_free_closed eb_link_m

theorem eb_link_delta_l {d} (ω κ L B J K V R F G u v : Term d) : (eb_link_m ω κ L B J K V R F G u v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (eb_edge_delta_l ..))))))

theorem eb_link_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L B J K V R F G u v : Term d) :
    Formula.satisfies ρ (eb_link_m ω κ L B J K V R F G u v) ↔
      Eb_link_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) (V.eval ρ)
        (R.eval ρ) (F.eval ρ) (G.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [eb_link_m, Eb_link_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, eb_edge_sat_l hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
