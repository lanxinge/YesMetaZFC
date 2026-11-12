import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.Source.Presentation
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.SetTheory.HereditaryCover
import YesMetaZFC.SetTheory.HereditarySequences
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 有限支撑代表的函数空间与拉回方程

代表始终是指定源集合中的真实函数图。坐标拉回用逐值方程表达，因而不依赖
中间函数空间、投影图或商模型的编码选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_space_d (κ n D : M.Domain) : Prop := ∀ s, M.mem s D ↔ Fn0_d n κ s
def ep_space_m {d} (κ n D : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest D.weaken) (fn0_m n.weaken κ.weaken .newest))
derive_free_closed ep_space_m
theorem ep_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ n D : Term d) :
    Formula.satisfies ρ (ep_space_m κ n D) ↔ Ep_space_d (κ.eval ρ) (n.eval ρ) (D.eval ρ) := by
  simp only [ep_space_m, Ep_space_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Ep_fun_d (κ X n f : M.Domain) : Prop := ∃ D, Ep_space_d κ n D ∧ Fn0_d D X f
def ep_fun_m {d} (κ X n f : Term d) : Formula 1 d := .existsE
  (.conj (ep_space_m κ.weaken n.weaken .newest) (fn0_m .newest X.weaken f.weaken))
derive_free_closed ep_fun_m
theorem ep_fun_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ X n f : Term d) :
    Formula.satisfies ρ (ep_fun_m κ X n f) ↔ Ep_fun_d (κ.eval ρ) (X.eval ρ) (n.eval ρ) (f.eval ρ) := by
  simp only [ep_fun_m, Ep_fun_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ep_space_sat_l hE, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Ep_fun_d.at_l (hE : Extensional M) {κ X n f D : M.Domain}
    (hf : Ep_fun_d κ X n f) (hD : Ep_space_d κ n D) : Fn0_d D X f := by
  obtain ⟨E, hE', hf⟩ := hf
  exact hE.eq_of_same_members E D (fun s => (hE' s).trans (hD s).symm) ▸ hf

def Ep_pull_d (κ X m n q f g : M.Domain) : Prop := Ep_fun_d κ X m f ∧ Ep_fun_d κ X n g ∧
  ∀ s r, Fn0_d n κ s → Cp0_d m n κ q s r → ∀ x, Rd_entry_d s x g ↔ Rd_entry_d r x f

def ep_pull_m {d} (κ X m n q f g : Term d) : Formula 1 d := .conj (ep_fun_m κ X m f)
  (.conj (ep_fun_m κ X n g) (.forallE (.forallE (.imp (fn0_m n.weaken.weaken κ.weaken.weaken (.bound 1))
    (.imp (cp0_m m.weaken.weaken n.weaken.weaken κ.weaken.weaken q.weaken.weaken (.bound 1) .newest)
      (.forallE (.iff (rd_entry_m (.bound 2) .newest g.weaken.weaken.weaken)
        (rd_entry_m (.bound 1) .newest f.weaken.weaken.weaken))))))))
derive_free_closed ep_pull_m
theorem ep_pull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ X m n q f g : Term d) :
    Formula.satisfies ρ (ep_pull_m κ X m n q f g) ↔
      Ep_pull_d (κ.eval ρ) (X.eval ρ) (m.eval ρ) (n.eval ρ) (q.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [ep_pull_m, Ep_pull_d, Formula.satisfies_conj_iff, ep_fun_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE, cp0_sat_l hE,
    Formula.satisfies_iff_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ep_pull_of_comp_l {κ X m n q D E t f g : M.Domain}
    (hD : Ep_space_d κ m D) (hE' : Ep_space_d κ n E) (ht : Fn0_d E D t) (hf : Fn0_d D X f)
    (spec : ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r)
    (h : Cp0_d E D X t f g) : Ep_pull_d κ X m n q f g :=
  ⟨⟨D, hD, hf⟩, ⟨E, hE', h.1⟩, fun s r hs hr _ => h.value_l ht hf ((spec s r).mpr ⟨(hE' s).mpr hs, hr⟩)⟩

theorem ep_pull_comp_l (hKP : M.Models KP) {κ X m n l q r t f g h : M.Domain}
    (hq : Fn0_d m n q) (hr : Fn0_d n l r) (ht : Cp0_d m n l q r t)
    (hfg : Ep_pull_d κ X m n q f g) (hgh : Ep_pull_d κ X n l r g h) : Ep_pull_d κ X m l t f h := by
  refine ⟨hfg.1, hgh.2.1, fun s u hs hu x => ?_⟩
  obtain ⟨v, hv⟩ := cp0_exists_l hKP hr hs
  obtain ⟨w, hw⟩ := cp0_exists_l hKP hq hv.1
  have e := cp0_unique_l hKP.1 ht.1 hs (Cp0_d.assoc_l hr hq ht hs hv hw) hu
  subst w
  exact (hgh.2.2 s v hs hv x).trans (hfg.2.2 v u hv.1 hw x)

theorem ep_pull_id_l (hE : Extensional M) {κ X n q f : M.Domain} (hf : Ep_fun_d κ X n f)
    (idq : ∀ i j, Rd_entry_d i j q → i = j) : Ep_pull_d κ X n n q f f := by
  refine ⟨hf, hf, fun s r hs hr x => ?_⟩
  have e : r = s := hr.1.ext_l hE hs fun i hi => by
    obtain ⟨j, _, y, _, hij, hjy, hiy⟩ := hr.2 i hi
    exact ⟨y, hiy, (idq i j hij).symm ▸ hjy⟩
  exact e ▸ Iff.rfl

theorem ep_pull_unique_l (hKP : M.Models KP) {κ X Y m n q f g h : M.Domain} (hq : Fn0_d m n q)
    (hg : Ep_pull_d κ X m n q f g) (hh : Ep_pull_d κ Y m n q f h) : g = h := by
  obtain ⟨E, he, hge⟩ := hg.2.1
  have hhe := hh.2.1.at_l hKP.1 he
  apply hge.ext_l hKP.1 hhe
  intro s hs
  obtain ⟨r, hr⟩ := cp0_exists_l hKP hq ((he s).mp hs)
  obtain ⟨x, _, hsx⟩ := hge.2.1 s hs
  exact ⟨x, hsx, (hh.2.2 s r ((he s).mp hs) hr x).mpr ((hg.2.2 s r ((he s).mp hs) hr x).mp hsx)⟩

/-- 扩大代表的值域界不改变坐标拉回方程。 -/
theorem Ep_pull_d.mono_l {κ X Y m n q f g : M.Domain} (h : Ep_pull_d κ X m n q f g)
    (sub : M.MemberSubset X Y) : Ep_pull_d κ Y m n q f g :=
  ⟨h.1.imp fun _ hh => ⟨hh.1, hh.2.mono_target_l sub⟩,
    h.2.1.imp fun _ hh => ⟨hh.1, hh.2.mono_target_l sub⟩, h.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界代表与共同支撑关系的有界原公式

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

/-! ## 背景编码与原模型自然数分离的源

Ω 编码背景的全部内部程序，w 是原关系中的自然数对象。分离、收集、
有限列及小坍塌由同一原关系解释；这些条件不要求整个载体传递。
实际隶属源继承此层，原关系后继也直接构造此层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

private theorem er_omega_closed_l : (Formula.isOmega (.newest : Term 1)).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed]

structure Er_source_d (Ω w κ K X R : M.Domain) : Prop where
  ext : Rf_ext_d I X R
  natural : Rr_truth_d I X R (Formula.isOmega .newest) (fun _ : Fin 1 => w)
  cardinal_small : Rf_small_d I X R κ
  finite : Sc_fseq_d I w κ K X R
  theory : Sc_theory_d I Ω X R
  collection : Sc_collection_d I Ω X R
  sequences : Sc_sequences_d I w X R
  collapse : Sc_collapse_d I X R

/-- 任意新的原关系小字母表，直接使用同一全称序列句子。 -/
theorem Er_source_d.rebase_l {Ω w κ K X R μ : M.Domain} (h : Er_source_d I Ω w κ K X R)
    (small : Rf_small_d I X R μ) : ∃ K', Er_source_d I Ω w μ K' X R := by
  obtain ⟨K', finite⟩ := h.sequences.space_l I small.mem_l
  exact ⟨K', h.ext, h.natural, small, finite, h.theory, h.collection, h.sequences, h.collapse⟩

/-- 原关系源沿实际全初等图回拉；新有限空间由全称序列句子自动给出。 -/
theorem Er_source_d.pull_l (hZF : M.Models ZF) {Ω w v κ μ K c d X R Y S j : M.Domain}
    (hΩ : M.IsOmega Ω) (h : Er_source_d I Ω v μ K Y S)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I Ω c d X Y j)
    (hw : M.PairMember I w v j) (hκ : M.PairMember I κ μ j) : ∃ L, Er_source_d I Ω w κ L X R := by
  have ext : Rf_ext_d I X R := by
    intro a ha b hb same
    obtain ⟨a', ha', aa⟩ := map.1.1.2.2 a ha
    obtain ⟨b', hb', bb⟩ := map.1.1.2.2 b hb
    have tr := smap_source_l I hZF hΩ mx my map (n := 2)
      (Formula.extensionalEq (.bound 1) .newest) (by simp -implicitDefEqProofs)
      ⟨Fin.cases ⟨b, hb⟩ (fun _ => ⟨a, ha⟩), fun _ => ⟨a, ha⟩⟩
      ⟨Fin.cases ⟨b', hb'⟩ (fun _ => ⟨a', ha'⟩), fun _ => ⟨a', ha'⟩⟩ (Fin.cases bb (fun _ => aa))
    have eq := h.ext a' ha' b' hb' (fun z hz =>
      (Formula.satisfies_extensionalEq_iff ..).mp
        (tr.mp ((Formula.satisfies_extensionalEq_iff ..).mpr (fun z => same z.val z.property))) ⟨z, hz⟩)
    exact map.1.2 a b a' aa (eq.symm ▸ bb)
  have hx := map.1.1.input_mem_of_pairMember hw
  have hy := map.1.1.output_mem_of_pairMember hw
  have natural : Rr_truth_d I X R (Formula.isOmega .newest) (fun _ : Fin 1 => w) := by
    apply (rr_truth_native_l I mx.2.1 _ er_omega_closed_l (fun _ => ⟨w, hx⟩)).mpr
    exact (smap_source_l I hZF hΩ mx my map (Formula.isOmega .newest) er_omega_closed_l
      ⟨fun _ => ⟨w, hx⟩, fun _ => ⟨w, hx⟩⟩ ⟨fun _ => ⟨v, hy⟩, fun _ => ⟨v, hy⟩⟩ (fun _ => hw)).mpr
        ((rr_truth_native_l I my.2.1 _ er_omega_closed_l (fun _ => ⟨v, hy⟩)).mp h.natural)
  have seq := (sc_sequences_iff_l I hZF hΩ mx my map hw).mpr h.sequences
  obtain ⟨L, finite⟩ := seq.space_l I (map.1.1.input_mem_of_pairMember hκ)
  exact ⟨L, ext, natural, (map.small_l I hZF hΩ mx my hκ).mpr h.cardinal_small, finite,
    h.theory.pull_l I hZF hΩ mx my map,
    h.collection.pull_l I hZF hΩ mx my (ext.native_l I mx.2.1) (h.ext.native_l I my.2.1) map,
    seq, (sc_collapse_iff_l I hZF hΩ mx my map).mpr h.collapse⟩

/-- 传递隶属实例中的自然数解释由实际背景 ω 给出。 -/
theorem Er_source_d.of_mem_l (hE : Extensional M) {ω c κ K X R : M.Domain}
    (hω : M.IsOmega ω) (trans : M.TransitiveSet X) (model : Smem_d I c X R) (hw : M.mem ω X)
    (small : Rf_small_d I X R κ) (finite : Sc_fseq_d I ω κ K X R) (theory : Sc_theory_d I ω X R)
    (collection : Sc_collection_d I ω X R) (sequences : Sc_sequences_d I ω X R) (collapse : Sc_collapse_d I X R) :
    Er_source_d I ω ω κ K X R := by
  refine ⟨rf_ext_mem_l I hE trans model, ?_, small, finite, theory, collection, sequences, collapse⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hw⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω, hw⟩, fun _ => ⟨ω, hw⟩⟩
  apply (rr_truth_native_l I model.1.2.1 (Formula.isOmega .newest) er_omega_closed_l (fun _ => ⟨ω, hw⟩)).mpr
  exact (smem_formula_l I model nx (Formula.isOmega .newest) ρ).mp
    ((Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l trans nx hE ⟨ω, hw⟩ hω))

/-- 完整自然数坐标确定后继源的真实自然数对象。 -/
theorem Er_source_d.of_layer_l (hKP : M.Models KP) {Ω w κ K X R z : M.Domain} (hΩ : M.IsOmega Ω)
    (ext : Rf_ext_d I X R) (numbers : Rr_layer_d I Ω X R w z)
    (small : Rf_small_d I X R κ) (finite : Sc_fseq_d I w κ K X R) (theory : Sc_theory_d I Ω X R)
    (collection : Sc_collection_d I Ω X R) (sequences : Sc_sequences_d I w X R) (collapse : Sc_collapse_d I X R) :
    Er_source_d I Ω w κ K X R := by
  refine ⟨ext, ?_, small, finite, theory, collection, sequences, collapse⟩
  let nx : ∃ x, M.mem x X := ⟨w, numbers.member⟩
  apply (rr_truth_native_l I nx (Formula.isOmega .newest) er_omega_closed_l (fun _ => ⟨w, numbers.member⟩)).mpr
  exact (Formula.satisfies_isOmega_iff ..).mpr (numbers.omega_l I hKP hΩ (ext.native_l I nx))

private theorem ep_closure_closed_l : (Definitional.Formula.conj sc_algebra_m sc_collapse_m).FreeClosed :=
  ⟨sc_algebra_closed_l, sc_collapse_closed_l⟩

def ep_closure_m {d} (X R : Term d) : Formula 1 d :=
  rr_rel_m kpair_convention_l (.conj sc_algebra_m sc_collapse_m) X R Fin.elim0

@[simp] theorem ep_closure_free_closed_l {d} (X R : Term d) (hx : X.freeSupport = []) (hr : R.freeSupport = []) :
    (ep_closure_m X R).FreeClosed := rr_rel_closed_l _ _ ep_closure_closed_l X R Fin.elim0 hx hr (fun i => Fin.elim0 i)

private theorem er_closure_sat_l {d} (ρ : Env M d) (X R : Term d) (nx : ∃ x, M.mem x (X.eval ρ)) :
    Formula.satisfies ρ (ep_closure_m X R) ↔
      (∀ ny : ∃ x, M.mem x (X.eval ρ), ∀ η : Env (smdl_structure_l I (R := R.eval ρ) ny) 0,
        Formula.satisfies η sc_algebra_m) ∧ Sc_collapse_d I (X.eval ρ) (R.eval ρ) := by
  have read (ny : ∃ x, M.mem x (X.eval ρ)) (η : Env (smdl_structure_l I (R := R.eval ρ) ny) 0) :=
    rr_rel_sat_l I ny (.conj sc_algebra_m sc_collapse_m) ep_closure_closed_l η ρ X R Fin.elim0 rfl rfl (fun i => Fin.elim0 i)
  constructor
  · intro h
    exact ⟨fun ny η => ((read ny η).mp h).1, fun ny η => ((read ny η).mp h).2⟩
  · rintro ⟨a, c⟩
    obtain ⟨x, hx⟩ := nx
    let η : Env (smdl_structure_l I (R := R.eval ρ) ⟨x, hx⟩) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
    exact (read ⟨x, hx⟩ η).mpr ⟨a _ η, c _ η⟩

def er_natural_m {d} (X R w : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) (Formula.isOmega .newest) X R (fun _ : Fin 1 => w)

@[simp] theorem er_natural_closed_l {d} (X R w : Term d)
    (hx : X.freeSupport = []) (hr : R.freeSupport = []) (hw : w.freeSupport = []) :
    (er_natural_m X R w).FreeClosed := rr_truth_closed_l _ er_omega_closed_l X R _ hx hr (fun _ => hw)

def er_source_m {d} (Ω w κ K X R : Term d) : Formula 1 d := set[d] ⟪
  ⌜rf_ext_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ) ∧ ⌜er_natural_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜w⌝ₛ) ∧
  ⌜rf_small_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜κ⌝ₛ) ∧
  ⌜sc_fseq_m (𝒞 := kpair_convention_l)⌝ₚ(⌜w⌝ₛ, ⌜κ⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜ep_closure_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ) ∧ ⌜sc_separation_m⌝ₚ(⌜Ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜sc_collection0_m⌝ₚ(⌜Ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧ ⌜sc_sequences0_m⌝ₚ(⌜w⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ)⟫
derive_free_closed er_source_m

/-- 原关系源整体可进入有限历史；两种自然数参数分别保存。 -/
theorem er_source_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Ω w κ K X R : Term d) :
    Formula.satisfies ρ (er_source_m Ω w κ K X R) ↔
      Er_source_d I (Ω.eval ρ) (w.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  have natural : Formula.satisfies ρ (er_natural_m X R w) ↔
      Rr_truth_d I (X.eval ρ) (R.eval ρ) (Formula.isOmega .newest) (fun _ : Fin 1 => w.eval ρ) :=
    rr_truth_sat_l I ρ _ er_omega_closed_l X R (fun _ => w)
  simp only [er_source_m, Formula.satisfies_conj_iff, rf_ext_sat_l I hE, natural,
    rf_small_sat_l I, sc_fseq_sat_l I, sc_separation_sat_l hE I, sc_sequences0_sat_l I]
  constructor
  · rintro ⟨ext, nw, small, finite, closure, sep, collect, seq⟩
    have hw : M.mem (w.eval ρ) (X.eval ρ) := nw.elim fun h _ => h 0
    obtain ⟨alg, collapse⟩ := (er_closure_sat_l I ρ X R ⟨w.eval ρ, hw⟩).mp closure
    exact ⟨ext, nw, small, finite, ⟨sep, alg⟩, (sc_collection0_sat_l I hE ρ Ω X R ext).mp collect, seq, collapse⟩
  · intro h
    have hw : M.mem (w.eval ρ) (X.eval ρ) := h.natural.elim fun h _ => h 0
    exact ⟨h.ext, h.natural, h.cardinal_small, h.finite,
      (er_closure_sat_l I ρ X R ⟨w.eval ρ, hw⟩).mpr ⟨h.theory.algebra, h.collapse⟩,
      h.theory.separation, (sc_collection0_sat_l I hE ρ Ω X R h.ext).mpr h.collection, h.sequences⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑系统的实际源数据

分离与集合代数适用于任意源内集合；统一化与塌缩只作用于源内小集合。这些性质
沿完整初等嵌入传递到后继模型。证书只使用配对解释，构造所需公理留在相应定理中。
全部函数空间、投影与代表拉回由此构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ep_source_d (I : kpair_convention_l.Interpretation M) (ω κ K X R : M.Domain) : Prop
    extends Er_source_d I ω ω κ K X R where
  omega : M.IsOmega ω
  below : M.MemberSubset ω κ
  transitive : M.TransitiveSet X
  omega_mem : M.mem ω X
  cardinal_mem : M.mem κ X
  code : ∃ c, Smem_d I c X R

theorem Ep_source_d.algebra_l (hKP : M.Models KP) {I : kpair_convention_l.Interpretation M}
    {ω κ K X R : M.Domain} (h : Ep_source_d I ω κ K X R) : Sc_algebra_d X := by
  obtain ⟨c, model⟩ := h.code
  exact h.theory.algebra_l I hKP h.transitive model

/-- 字面大小界仅在实际传递隶属实例中读取。 -/
theorem Ep_source_d.cardinal_small_l (hKP : M.Models KP) {I : kpair_convention_l.Interpretation M}
    {ω κ K X R : M.Domain} (h : Ep_source_d I ω κ K X R) : Sc_small_d X κ := by
  obtain ⟨c, model⟩ := h.code
  exact (rf_small_mem_l I hKP h.transitive model h.cardinal_mem).mp h.cardinal_small

/-- 指定有限空间通过实际隶属实例读取；完整性来自有限图闭包。 -/
theorem Ep_source_d.finite_l (hKP : M.Models KP) {I : kpair_convention_l.Interpretation M}
    {ω κ K X R : M.Domain} (h : Ep_source_d I ω κ K X R) : Fseq_space_d (kp_pair_l hKP) ω κ K := by
  obtain ⟨c, model⟩ := h.code
  have a := h.algebra_l hKP
  exact (sc_fseq_mem_l I hKP h.omega h.transitive model h.omega_mem h.cardinal_mem h.finite.mem_l a.pair a.union).mp h.finite

/-- 传递隶属实例把原关系中的有限列句子读为实际空间与编号。 -/
theorem Ep_source_d.sequences_l (hKP : M.Models KP) {I : kpair_convention_l.Interpretation M}
    {ω κ K X R : M.Domain} (h : Ep_source_d I ω κ K X R) :
    (∀ A, M.mem A X → ∃ K, M.mem K X ∧ Fseq_space_d (kp_pair_l hKP) ω A K) ∧
    (∀ A K μ e, M.mem A X → M.mem K X → M.mem μ X → M.mem e X →
      Fseq_space_d (kp_pair_l hKP) ω A K → M.MemberSubset ω μ → Sc_index_d μ A e →
        ∃ f, M.mem f X ∧ Sc_index_d μ K f) := by
  obtain ⟨c, model⟩ := h.code
  have a := h.algebra_l hKP
  exact (sc_sequences_mem_l I hKP h.omega h.transitive model h.omega_mem a.pair a.union).mp h.sequences

/-- 新字母表的小性由源内实际单射给出。 -/
theorem Ep_source_d.rebase_l {I : kpair_convention_l.Interpretation M} {ω κ K X R μ : M.Domain}
    (h : Ep_source_d I ω κ K X R) (hμ : M.mem μ X) (hωμ : M.MemberSubset ω μ) (small : Rf_small_d I X R μ) :
    ∃ K', Ep_source_d I ω μ K' X R := by
  obtain ⟨K', core⟩ := h.toEr_source_d.rebase_l I small
  exact ⟨K', core, h.omega, hωμ, h.transitive, h.omega_mem, hμ, h.code⟩

/-- 全部内部有限 κ 列具有源内的同一 κ 编号。 -/
theorem Ep_source_d.finite_index_l (hZF : M.Models ZF) {ω κ K X R : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hκ : M.IsOrdinal κ) : ∃ e, M.mem e X ∧ M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) e K κ := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨f, hf, fn, graph⟩ := sc_identity_l hZF source.omega source.transitive hc source.theory source.cardinal_mem
  have idx : Sc_index_d κ κ f := Sc_index_d.of_injection_l (ZF.modelsKP hZF) hκ
    ⟨fn0_function_l (ZF.modelsKP hZF) fn,
      fun a b x ha hb => ((graph a x).mp ha).2.trans ((graph b x).mp hb).2.symm⟩
  obtain ⟨e, he, index⟩ := (source.sequences_l (ZF.modelsKP hZF)).2 κ K κ f source.cardinal_mem source.finite.mem_l source.cardinal_mem hf (source.finite_l (ZF.modelsKP hZF)) source.below idx
  exact index.restrict_l hZF source.omega source.transitive hc source.theory source.finite.mem_l source.cardinal_mem he

theorem Ep_source_d.space_l (hZF : M.Models ZF) {ω κ K X R n : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω) : ∃ D, M.mem D X ∧ Ep_space_d κ n D := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, hm⟩ := h.code
  let φ : Delta0UnarySchema 2 := { body := fn0_m (.bound 2) (.bound 1) .newest, delta0 := fn0_delta_l .. }
  let ρ : Env M 2 := (⟨fun _ => n, fun _ => n⟩ : Env M 1).push κ
  obtain ⟨D, hDX, hd⟩ := sc_separate_source_l I hZF h.omega h.transitive hm h.theory
    φ.toUnarySchema φ.delta0 ρ (Fin.cases h.cardinal_mem (fun _ => h.transitive ω h.omega_mem n hn)) h.finite.mem_l
  refine ⟨D, hDX, fun s => (hd s).trans ?_⟩
  have sat : φ.toUnarySchema.denote ρ s ↔ Fn0_d n κ s := fn0_sat_l hZF.1 _ _ _ _
  exact (and_congr_right fun _ => sat).trans ⟨And.right, fun hs =>
    ⟨((h.finite_l (ZF.modelsKP hZF)) s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hs⟩, hs⟩⟩

theorem Ep_source_d.space_mem_l (hZF : M.Models ZF) {ω κ K X R n D : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) : M.mem D X := by
  obtain ⟨E, he, hs⟩ := h.space_l hZF hn
  exact hZF.1.eq_of_same_members E D (fun s => (hs s).trans (hD s).symm) ▸ he

theorem Ep_source_d.uniform_l (hZF : M.Models ZF) {ω κ K X R n D : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) :
    Sc_uniform_d (kp_pair_l (ZF.modelsKP hZF)) ω X R D := by
  obtain ⟨c, hc⟩ := h.code
  exact (sc_collection_mem_l _ (ZF.modelsKP hZF) h.transitive hc).mp h.collection D (h.space_mem_l hZF hn hD)
    ((h.sequences.small_l hZF h.omega h.transitive hc h.theory h.omega_mem h.cardinal_mem h.finite.mem_l (h.finite_l (ZF.modelsKP hZF)) (h.cardinal_small_l (ZF.modelsKP hZF))).mono_l
      (fun s hs => ((h.finite_l (ZF.modelsKP hZF)) s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hs)⟩))

theorem Ep_source_d.function_l (hZF : M.Models ZF) {ω κ K X R D f : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hf : M.mem f X)
    (hF : Fn0_d D X f) : Sfun_d X D f := sc_function_domain_l (h.algebra_l (ZF.modelsKP hZF)) hf hF

theorem Ep_source_d.projection_l (hZF : M.Models ZF) {ω κ K X R m n q D E : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hm : M.mem m ω) (hn : M.mem n ω)
    (hq : Fn0_d m n q) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E) :
    ∃ t, M.mem t X ∧ Fn0_d E D t ∧ ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r := by
  obtain ⟨c, hM⟩ := h.code
  have hqX := h.transitive K h.finite.mem_l q (((h.finite_l (ZF.modelsKP hZF)) q).mpr ⟨m, hm,
    fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l fun i hi => h.below i (h.omega.transitive (ZF.modelsKP hZF) n hn i hi))⟩)
  exact sc_reindex_l hZF h.omega h.transitive hM h.theory
    (h.transitive ω h.omega_mem m hm) (h.transitive ω h.omega_mem n hn) h.cardinal_mem hqX
    (h.space_mem_l hZF hn hE) hq hD hE

theorem Ep_source_d.family_l (hZF : M.Models ZF) {ω κ K X R m n q D E F G : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hm : M.mem m ω) (hn : M.mem n ω)
    (hq : Fn0_d m n q) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (hF : ∀ f, M.mem f F ↔ M.mem f X ∧ Fn0_d D X f) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d E X g) :
    ∃ t P, M.mem t X ∧ Fn0_d E D t ∧
      (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) P F G ∧
      ∀ f g, Rd_entry_d f g P ↔ M.mem f F ∧ M.mem g G ∧ Cp0_d E D X t f g := by
  obtain ⟨t, htX, ht, spec⟩ := h.projection_l hZF hm hn hq hD hE
  obtain ⟨c, hM⟩ := h.code
  obtain ⟨P, hp, hs⟩ := rs_pullback_family_l hZF h.omega h.transitive hM h.theory
    (h.space_mem_l hZF hn hE) (h.space_mem_l hZF hm hD) htX ht hF hG
  exact ⟨t, P, htX, ht, spec, hp, hs⟩

theorem Ep_source_d.model_l (hZF : M.Models ZF) {ω κ K X R n D U : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω)
    (hD : Ep_space_d κ n D) (hU : FilterZF.Base_d (ℳ := M) D U) (S : M.Domain) : ∃ G c p C T,
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧
      Rp_model_d (kp_pair_l (ZF.modelsKP hZF)) D X U S c G p C T := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, hM⟩ := h.code
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := sc_constant_l hZF h.omega h.transitive hM h.theory
    (h.space_mem_l hZF hn hD) h.cardinal_mem
  exact rp_family_model_l I hZF hU hfX (hf.mono_target_l (h.transitive A hAX)) S

/-- 正则 Hχ 给出初始源理论及全部字母表的实际有限序列空间。 -/
theorem ep_source_of_h_l (hZFC : M.Models ZFC) {ω κ K χ X : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X) (hωX : M.mem ω X) (hκX : M.mem κ X)
    (hKX : M.mem K X) (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K) :
    ∃ R, Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.h_transitive_l I hZF hX
  obtain ⟨c, R, hc, hr⟩ := smdl_membership_l I hZF ⟨κ, hκX⟩
  have theory := sc_h_theory_l hZFC hω hχ hωχ hX R ⟨hc, hr⟩
  have a := theory.algebra_l I (ZF.modelsKP hZF) ht ⟨hc, hr⟩
  have finite := (sc_fseq_mem_l I (ZF.modelsKP hZF) hω ht ⟨hc, hr⟩ hωX hκX hKX a.pair a.union).mpr hK
  have core := Er_source_d.of_mem_l I hZF.1 hω ht ⟨hc, hr⟩ hωX
    ((rf_small_mem_l I (ZF.modelsKP hZF) ht ⟨hc, hr⟩ hκX).mpr (sc_h_small_l hZFC hω hχ hωχ hX hκX))
    finite theory (sc_h_collection_l hZFC hω hχ hωχ hX R ⟨hc, hr⟩)
    (sc_h_sequences_l hZFC hω hχ hωχ hX ⟨hc, hr⟩) (sc_h_collapse_l hZFC hω hχ hωχ hX ⟨hc, hr⟩)
  exact ⟨R, core, hω, hωκ, ht, hωX, hκX, c, hc, hr⟩

/-- 传递初等后继在任意源内小参数 κ′ 上重新成为源；无需 κ′ 在旧嵌入的像中。 -/
theorem Ep_source_d.successor_l (hZF : M.Models ZF) {ω κ K X R c d N W j κ' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W) (hN : M.TransitiveSet N)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X N j)
    (hκ : M.mem κ' N) (hωκ : M.MemberSubset ω κ') (small : Rf_small_d (kp_pair_l (ZF.modelsKP hZF)) N W κ') : ∃ K', Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' N W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have theory := source.theory.map_l I hZF source.omega hm.1 hn.1 hj
  have hw := hj.omega_l I hZF source.omega source.transitive hN hm hn source.omega_mem
  have hωN := hj.1.1.output_mem_of_pairMember hw
  have seq := (sc_sequences_iff_l I hZF source.omega hm.1 hn.1 hj hw).mp source.sequences
  obtain ⟨K', space⟩ := seq.space_l I hκ
  have core := Er_source_d.of_mem_l I hZF.1 source.omega hN hn hωN small space theory
    (source.collection.map_l I hZF source.omega hm.1 hn.1 (source.ext.native_l I hm.1.2.1)
      (rf_ext_mem_l I hZF.1 hN hn |>.native_l I hn.1.2.1) hj) seq
    ((sc_collapse_iff_l I hZF source.omega hm.1 hn.1 hj).mp source.collapse)
  exact ⟨K', core, source.omega, hωκ, hN, hωN, hκ, d, hn⟩

/-- 自动覆盖指定参数，并包含有限 κ 幂的全部子集；可分别用作所属模型与施加源。 -/
theorem ep_source_exists_l (hZFC : M.Models ZFC) (A : M.Domain) {ω κ : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ) :
    ∃ K X R, Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R ∧ M.mem A X ∧
      ∀ n D B, M.mem n ω → Ep_space_d κ n D → M.MemberSubset B D → M.mem B X := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) κ K
  obtain ⟨B, hB⟩ := KP.exists_pair (ZF.modelsKP hZF) ω A
  obtain ⟨Q, hQ⟩ := KP.exists_pair (ZF.modelsKP hZF) B P
  obtain ⟨χ, X, hχ, hωχ, hX, hQX⟩ := ZFC.h_cover_l I hZFC hω Q
  have ht := ZF.h_transitive_l I hZF hX
  have hBX := ht Q hQX B ((hQ B).mpr (Or.inl rfl))
  have hPX := ht Q hQX P ((hQ P).mpr (Or.inr rfl))
  have hKX := ht P hPX K ((hP K).mpr (Or.inr rfl))
  obtain ⟨R, hR⟩ := ep_source_of_h_l hZFC hω hωκ hχ hωχ hX
    (ht B hBX ω ((hB ω).mpr (Or.inl rfl))) (ht P hPX κ ((hP κ).mpr (Or.inl rfl))) hKX hK
  exact ⟨K, X, R, hR, ht B hBX A ((hB A).mpr (Or.inr rfl)), fun n D B hn hD hBD =>
    ZF.h_subsets_l I hZF hχ.isLimitOrdinal hX hKX B fun s hs =>
      (hK s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((hD s).mp (hBD s hs))⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部有界源代表组成的源内节点集

所有有限定义域都包含在同一个有限 κ 列空间中，因此一个相对幂集足以
容纳任意有限支撑的 B 值函数。节点只取这批原有函数，不增添外部代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Eb_pool_d (ω κ L X B J K P G A : M.Domain) : Prop where
  indices : M.mem J X
  powers : M.mem P X
  functions : M.mem G X
  carrier : M.mem A X
  subsets : FilterZF.Source_d X K P
  graphs : ∀ f, M.mem f G ↔ M.mem f X ∧
    ∀ p, M.mem p f → ∃ s, M.mem s K ∧ ∃ x, M.mem x B ∧ KPair_d M p s x
  nodes : ∀ u, M.mem u A ↔ Eb_node_d ω κ L K B J G P u

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_indices_mem_l {ω κ K X R L J : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hL : M.mem L X) (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) : M.mem J X := by
  obtain ⟨S, hS, seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L hL
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 2 := ⟨Fin.cases L (fun _ => ω), fun _ => L⟩
  let φ : UnarySchema 2 := { body := ei_m (.bound 2) (.bound 1) .newest }
  obtain ⟨J', hJ', spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ
    (ei_delta_l ..) ρ (Fin.cases hL (fun _ => source.omega_mem)) hS
  have eq : J' = J := hZF.1.eq_of_same_members J' J (fun a => by
    have read : φ.denote ρ a ↔ Ei_d ω L a := ei_sat_l hZF.1 ..
    rw [spec a, read, indices a]
    exact ⟨And.right, fun h => ⟨(seq a).mpr (h.elim fun n hn =>
      ⟨n, hn.1, fn0_function_l (ZF.modelsKP hZF) hn.2.1⟩), h⟩⟩)
  exact eq ▸ hJ'

theorem eb_pool_l {ω κ K X R L J B : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (power : Sc_power_d X) (hL : M.mem L X) (hB : M.mem B X)
    (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) : ∃ P G A, Eb_pool_d ω κ L X B J K P G A := by
  obtain ⟨c, code⟩ := source.code
  have hJ := ep_indices_mem_l hZF source hL indices
  obtain ⟨P, hP, subsets⟩ := power K source.finite.mem_l
  obtain ⟨Q, hQ, product⟩ := (source.algebra_l (ZF.modelsKP hZF)).product K B source.finite.mem_l hB
  obtain ⟨G, hG, graphs⟩ := power Q hQ
  obtain ⟨V, hV, pair⟩ := (source.algebra_l (ZF.modelsKP hZF)).product J G hJ hG
  let ρ : Env M 8 := ⟨Fin.cases P (Fin.cases G (Fin.cases J (Fin.cases B
    (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω))))))), fun _ => ω⟩
  let φ : UnarySchema 8 := {
    body := eb_node_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨A, hA, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ (eb_node_delta_l ..) ρ
    (Fin.cases hP (Fin.cases hG (Fin.cases hJ (Fin.cases hB (Fin.cases source.finite.mem_l
      (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))) hV
  refine ⟨P, G, A, hJ, hP, hG, hA, subsets, fun f => (graphs f).trans
    (and_congr_right fun _ => ⟨fun h p hp => (product p).mp (h p hp), fun h p hp => (product p).mpr (h p hp)⟩), fun u => ?_⟩
  exact (spec u).trans ((and_congr_right fun _ => eb_node_sat_l hZF.1 ..).trans
    ⟨And.right, fun h => ⟨h.elim (fun a ha => ha.2.elim (fun f hf => (pair u).mpr ⟨a, ha.1, f, hf.1, hf.2.1⟩)), h⟩⟩)

theorem Eb_pool_d.read_l (hKP : M.Models KP) {ω κ K X L B J P G A u : M.Domain}
    (finite : Fseq_space_d (kp_pair_l hKP) ω κ K)
    (pool : Eb_pool_d ω κ L X B J K P G A) (hu : M.mem u A) : ∃ n a D f,
      M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ KPair_d M u a f := by
  obtain ⟨a, ha, f, hf, pair, n, hn, D, _, hna, space, fn⟩ := (pool.nodes u).mp hu
  exact ⟨n, a, D, f, hn, ha, hna, (eb_space_iff_l hKP finite hn).mp space,
    ((pool.graphs f).mp hf).1, fn, pair⟩

theorem Eb_pool_d.node_l (hKP : M.Models KP) {ω κ K X L B J P G A n a D f u : M.Domain}
    (finite : Fseq_space_d (kp_pair_l hKP) ω κ K)
    (pool : Eb_pool_d ω κ L X B J K P G A) (hn : M.mem n ω) (ha : M.mem a J) (fn : Fn0_d n L a)
    (space : Ep_space_d κ n D) (hD : M.mem D X) (hf : M.mem f X) (ff : Fn0_d D B f) (hu : KPair_d M u a f) : M.mem u A := by
  have dk s (hs : M.mem s D) : M.mem s K := (finite s).mpr ⟨n, hn, fn0_function_l hKP ((space s).mp hs)⟩
  exact (pool.nodes u).mpr ⟨a, ha, f, (pool.graphs f).mpr ⟨hf, fun p hp =>
    (ff.1 p hp).elim fun s hs => hs.2.elim fun x hx => ⟨s, dk s hs.1, x, hx⟩⟩, hu,
    n, hn, D, (pool.subsets D).mpr ⟨hD, dk⟩, fn,
      (eb_space_iff_l hKP finite hn).mpr space, ff⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 正则秩层本身的源实例

源就是 Vδ。全内部分离与有限集合代数适用于极限秩层；小定义域统一化
使用 δ 的正则性。此处没有强极限前提，也不再通过 Vδ=Hδ 改换源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 测度图的支撑与有限 κ 列给出统一秩界，故整张扩展器属于原极限秩层。 -/
theorem Em_family_d.rank_mem_l (hZF : M.Models ZF) {ω κ L F δ X : M.Domain}
    (family : Em_family_d ω κ L F) (graph : M.IsSetRelation (kp_pair_l (ZF.modelsKP hZF)) F)
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (hωX : M.mem ω X) (hκX : M.mem κ X) (hLX : M.mem L X) : M.mem F X := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω L
  have hKX := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hκX hK
  have hSX := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hLX hS
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF K
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  have hQX := v_power_mem_l I hX hδ (v_power_mem_l I hX hδ hKX hP) hQ
  obtain ⟨B, hB, hSB, hQB⟩ := v_joint_bound_l I hX hSX hQX
  apply v_relation_mem_l I hX hδ hB
  intro p hp
  obtain ⟨a, U, pair⟩ := graph p hp
  obtain ⟨n, D, hn, ha, hd, hu⟩ := family.measure a U ⟨p, pair, hp⟩
  refine ⟨a, hSB a ((hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩), U, hQB U ((hQ U).mpr ?_), pair⟩
  intro A hA
  exact (hP A).mpr (fun s hs => (hK s).mpr ⟨n, hn,
    fn0_function_l (ZF.modelsKP hZF) ((hd s).mp (hu.1.1 A hA s hs))⟩)

theorem ep_regular_source_l (hZFC : M.Models ZFC) {ω δ V κ K : M.Domain}
    (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V)
    (hκ : M.mem κ δ) (hωκ : M.MemberSubset ω κ)
    (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K) :
    ∃ R, Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hκV := ZF.v_ordinal_mem_l I hZF hV hκ
  have hωV := ZF.v_ordinal_mem_l I hZF hV hωδ
  have ht := v_transitive_l I hV
  obtain ⟨c, R, hc, code⟩ := smdl_membership_l I hZF ⟨κ, hκV⟩
  have theory := sc_v_theory_l hZFC hr.isLimitOrdinal hV ω R ⟨hc,code⟩
  have a := theory.algebra_l I (ZF.modelsKP hZF) ht ⟨hc, code⟩
  have hk := ZF.v_fseq_mem_l I hZF hV hr.isLimitOrdinal hω hωV hκV hK
  have finite := (sc_fseq_mem_l I (ZF.modelsKP hZF) hω ht ⟨hc, code⟩ hωV hκV hk a.pair a.union).mpr hK
  have core := Er_source_d.of_mem_l I hZF.1 hω ht ⟨hc, code⟩ hωV
    (sc_ordinal_small_l hZF hω ht ⟨hc, code⟩ theory hκV (hr.isCardinal.1.mem hκ)) finite theory
    (sc_v_collection_l hZFC hr hV ω R ⟨hc, code⟩) (sc_v_sequences_l hZF hω hr.isLimitOrdinal hωδ hV ⟨hc, code⟩)
    (sc_v_collapse_l hZF hr.isCardinal hr.isLimitOrdinal hV ⟨hc, code⟩)
  exact ⟨R, core, hω, hωκ, ht, hωV, hκV, c, hc, code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑源证书的一阶编码

证书仍是实际的全内部分离、小定义域统一化、有限列空间与塌缩性质。
集合代数及小关系坍塌共同解释在原关系中；同一编码供历史分离和实际源构造使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

def ep_source_m {d} (ω κ K X R : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ Trans(⌜X⌝ₛ) ∧ ⌜ω⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜X⌝ₛ ∧
  ⌜ω⌝ₛ ⊆ ⌜κ⌝ₛ ∧ (∃ c, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, ⌜X⌝ₛ, ⌜R⌝ₛ)) ∧
  ⌜er_source_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ)⟫
derive_free_closed ep_source_m

theorem ep_source_sat_l {d} (ρ : Env M d) (ω κ K X R : Term d) :
    Formula.satisfies ρ (ep_source_m ω κ K X R) ↔ Ep_source_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [ep_source_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, smem_sat_l I, er_source_sat_l I hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hw, ht, hω, hκ, below, model, core⟩ => ⟨core, hw, below, ht, hω, hκ, model⟩,
    fun h => ⟨h.omega, h.transitive, h.omega_mem, h.cardinal_mem, h.below, h.code, h.toEr_source_d⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 所属源内的完整支撑迹

只用原测度、代表函数及有限坐标作有界分离。保留实际分离集和计算数据，
以便沿所属源的嵌入搬运后，在原超幂与复制超幂中读取同一个集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_trace_d (ω κ L K X F m D E a f Z : M.Domain) : Prop := ∃ B J U R ι T,
  M.mem B X ∧ M.mem J X ∧ M.mem U X ∧ M.mem R X ∧ M.mem ι X ∧ M.mem T X ∧
    M.MemberSubset K B ∧ (∀ s, M.mem s J ↔ Ei_d ω L s) ∧
    Rd_fun_d .range F F F U ∧ Rd_fun_d .mem B B B R ∧ Fn0_d D B f ∧ Fn0_d E E ι ∧
    (∀ s, M.mem s E → Rd_entry_d s s ι) ∧
    (∀ t, M.mem t T ↔ ∃ n, M.mem n ω ∧ Fn0_d n L t) ∧ M.MemberSubset Z T ∧
    ∀ t, M.mem t T → (M.mem t Z ↔ Fn0_d m L t ∧ Eb_edge_d ω κ L B J K U R F t ι a f)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem eb_trace_l {ω κ K L X R F J m D E a f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hL : M.mem L X) (hF : M.mem F X)
    (indices : ∀ s, M.mem s J ↔ Ei_d ω L s) (ha : M.mem a J)
    (hm : M.mem m ω) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (ff : Fn0_d D X f) :
    ∃ Z, M.mem Z X ∧ Eb_trace_d ω κ L K X F m D E a f Z := by
  obtain ⟨c, code⟩ := source.code
  have hJ := ep_indices_mem_l hZF source hL indices
  have haX := source.transitive J hJ a ha
  obtain ⟨P, hP, coords⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hfX
  obtain ⟨Q, hQ, pair⟩ := (source.algebra_l (ZF.modelsKP hZF)).pair P K hP source.finite.mem_l
  obtain ⟨B, hB, union⟩ := (source.algebra_l (ZF.modelsKP hZF)).union Q hQ
  have pb x (hx : M.mem x P) : M.mem x B := (union x).mpr ⟨P, (pair P).mpr (Or.inl rfl), hx⟩
  have kb x (hx : M.mem x K) : M.mem x B := (union x).mpr ⟨K, (pair K).mpr (Or.inr rfl), hx⟩
  have fb : Fn0_d D B f := ff.retarget_l (fun s x hsx => pb x (coords s x hsx).2)
  let membership : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨R₀, hR₀, shape, rel⟩ := sc_relation_source_l hZF source.omega source.transitive code source.theory membership (.mem ..)
    ⟨Fin.elim0, fun _ => B⟩ (fun i => Fin.elim0 i) hB hB
  have relation x y : Rd_entry_d x y R₀ ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have membership₀ : Rd_fun_d .mem B B B R₀ := by
    intro p
    refine ⟨fun hp => ?_, ?_⟩
    · obtain ⟨x, y, pair⟩ := shape p hp
      obtain ⟨hx, hy, hxy⟩ := (relation x y).mp ⟨p, pair, hp⟩
      exact ⟨x, y, hx, hy, hxy, pair⟩
    · rintro ⟨x, y, hx, hy, hxy, pair⟩
      obtain ⟨q, qp, hq⟩ := (relation x y).mpr ⟨hx, hy, hxy⟩
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
  obtain ⟨U, hU, range⟩ := sc_range_source_l hZF source.omega source.transitive code source.theory hF
  let equal : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ε : Env M 0 := ⟨Fin.elim0, fun _ => E⟩
  have eqs u x : equal.denote ε u x ↔ x = u := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  have hEX := source.space_mem_l hZF hm hE
  obtain ⟨ι, hι, fi, is⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory equal (.atom ..) ε
    (fun i => Fin.elim0 i) hEX hEX (fun u hu => ⟨u, hu, (eqs u u).mpr rfl⟩)
  obtain ⟨T, hT, seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L hL
  let ρ : Env M 13 := ⟨Fin.cases m (Fin.cases f (Fin.cases a (Fin.cases ι (Fin.cases F (Fin.cases R₀ (Fin.cases U
    (Fin.cases K (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases κ (fun _ => ω)))))))))))), fun _ => ω⟩
  let φ : UnarySchema 13 := {
    body := .conj (fn0_m (.bound 1) (.bound 11) .newest)
      (eb_edge_m (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
        (.bound 6) (.bound 5) .newest (.bound 4) (.bound 3) (.bound 2)) }
  have sat t : φ.denote ρ t ↔ Fn0_d m L t ∧ Eb_edge_d ω κ L B J K U R₀ F t ι a f :=
    (Formula.satisfies_conj_iff ..).trans (and_congr (fn0_sat_l hZF.1 ..) (eb_edge_sat_l hZF.1 ..))
  obtain ⟨Z, hZ, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ
    (.conj (fn0_delta_l ..) (eb_edge_delta_l ..)) ρ
    (Fin.cases (source.transitive ω source.omega_mem m hm) (Fin.cases hfX (Fin.cases haX (Fin.cases hι (Fin.cases hF
      (Fin.cases hR₀ (Fin.cases hU (Fin.cases source.finite.mem_l (Fin.cases hJ (Fin.cases hB (Fin.cases hL
        (Fin.cases source.cardinal_mem (fun _ => source.omega_mem))))))))))))) hT
  refine ⟨Z, hZ, B, J, U, R₀, ι, T, hB, hJ, hU, hR₀, hι, hT, kb, indices, range, membership₀, fb, fi, ?_, ?_,
    (fun t ht => ((spec t).mp ht).1), fun t ht => (spec t).trans ((and_iff_right ht).trans (sat t))⟩
  · intro s hs
    obtain ⟨x, _, hsx⟩ := fi.2.1 s hs
    exact (eqs s x).mp (is s x hsx) ▸ hsx
  · exact fun t => (seq t).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)

end YesMetaZFC.SetTheory.LargeCardinal
