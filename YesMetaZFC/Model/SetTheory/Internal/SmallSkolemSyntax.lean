import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.Model.SetTheory.Reflection.SkolemSyntax
import YesMetaZFC.SetTheory.FinitaryHullSyntax
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 内部公式的两个实参

依次更新两个坐标，把统一满足关系作为实际二元公式使用。原程序和参数赋值
都保留为模型内集合，供内部收集与见证统一化消费。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sbin_d (X R E F n r i j f x y : M.Domain) : Prop := ∃ g h,
  Senv_update_d I f i x g ∧ Senv_update_d I g j y h ∧ Ssat_d I X R E F n r h

def sbin_m {d} (X R E F n r i j f x y : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (senv_update_m (𝒞 := 𝒞) f.weaken.weaken i.weaken.weaken x.weaken.weaken (.bound 1))
    (.conj (senv_update_m (𝒞 := 𝒞) (.bound 1) j.weaken.weaken y.weaken.weaken .newest)
      (ssat_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken E.weaken.weaken
        F.weaken.weaken n.weaken.weaken r.weaken.weaken .newest))))
derive_free_closed sbin_m

theorem sbin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R E F n r i j f x y : Term d) :
    Formula.satisfies ρ (sbin_m (𝒞 := 𝒞) X R E F n r i j f x y) ↔
      Sbin_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ)
        (i.eval ρ) (j.eval ρ) (f.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [sbin_m, Sbin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    senv_update_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem sbin_update_l (hE : Extensional M) {X R E F n r i j f x y g} (hu : Senv_update_d I f i x g) :
    Sbin_d I X R E F n r i j f x y ↔ ∃ h, Senv_update_d I g j y h ∧ Ssat_d I X R E F n r h := by
  refine ⟨?_, fun ⟨h, hh, ht⟩ => ⟨g, h, hu, hh, ht⟩⟩
  rintro ⟨g', h, hg, hh, ht⟩
  exact ⟨h, senv_update_unique_l I hE hg hu ▸ hh, ht⟩

theorem sbin_value_l (hE : Extensional M) {X R E F n r i j f x y g h}
    (hu : Senv_update_d I f i x g) (hv : Senv_update_d I g j y h) :
    Sbin_d I X R E F n r i j f x y ↔ Ssat_d I X R E F n r h :=
  (sbin_update_l I hE hu).trans ⟨fun ⟨_, hh, ht⟩ => senv_update_unique_l I hE hh hv ▸ ht,
    fun ht => ⟨h, hv, ht⟩⟩

theorem sbin_agree_l (hZF : M.Models ZF) {ω X R E F n r i j f g b x y}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hE : M.IsFunctionSpace I E ω X)
    (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g) (hx : M.mem x X) (hy : M.mem y X) :
    Sbin_d I X R E F n r i j f x y ↔ Sbin_d I X R E F n r i j g x y := by
  obtain ⟨u, hu, huf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
  obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF huf hj hy
  obtain ⟨w, hw, hwf⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi hx
  obtain ⟨z, hz, hzf⟩ := senv_update_exists_l I hZF hwf hj hy
  exact (sbin_value_l I hZF.1 hu hv).trans ((ssat_agree_l I hZF hF hb hE hr
    ((hE v).mpr hvf) ((hE z).mpr hzf) ((ha.update_l I hu hw).update_l I hv hz)).trans
      (sbin_value_l I hZF.1 hw hz).symm)

def Scollect_d (X R E F n r i j f D C : M.Domain) : Prop := ∀ x, M.mem x D →
  ∃ y, M.mem y C ∧ Sbin_d I X R E F n r i j f x y

theorem scollect_agree_l (hZF : M.Models ZF) {ω X R E F n r i j f g b D C}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hE : M.IsFunctionSpace I E ω X)
    (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g)
    (hD : M.MemberSubset D X) (hC : M.MemberSubset C X) :
    Scollect_d I X R E F n r i j f D C ↔ Scollect_d I X R E F n r i j g D C :=
  forall_congr' fun x => imp_congr_right fun hx => exists_congr fun y => and_congr_right fun hy =>
    sbin_agree_l I hZF hF hb hr hi hj hE hf hg ha (hD x hx) (hC y hy)

end YesMetaZFC.SetTheory.Internal

/-! ## 不同变量域上的同一内部公式

赋值空间只需包含程序实际读取的坐标。对原指令作内部强归纳，有限赋值
与完整 ω 赋值具有相同真值；量词步同时更新两份赋值，不引入外部递归。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssat_spaces_l (hZF : M.Models ZF) {ω X R E D V W F n b r f g : M.Domain}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b)
    (hE : M.IsFunctionSpace I E V X) (hD : M.IsFunctionSpace I D W X)
    (hV : M.MemberSubset b V) (hW : M.MemberSubset b W) (hr : M.mem r n)
    (hf : M.mem f E) (hg : M.mem g D) (agree : Senv_agree_d I b f g) :
    Ssat_d I X R E F n r f ↔ Ssat_d I X R D F n r g := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF X R D F hF.2.1.1
  let ρ : Env M 7 := ⟨Fin.cases b (Fin.cases n (Fin.cases F (Fin.cases D
    (Fin.cases E (Fin.cases R (fun _ => X)))))), fun _ => X⟩
  let φ : UnarySchema 7 := {
    body := Formula.forallMem (.bound 5) (Formula.forallMem (.bound 5)
      (.imp (senv_agree_m (𝒞 := 𝒞) (.bound 3) (.bound 1) .newest)
        (.iff (ssat_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
          (ssat_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have sat k : φ.denote ρ k ↔ ∀ f, M.mem f E → ∀ g, M.mem g D → Senv_agree_d I b f g →
      (Ssat_d I X R E F n k f ↔ Ssat_d I X R D F n k g) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, senv_agree_sat_l I, ssat_sat_l I hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr) f hf g hg agree
  intro k hk ih
  apply (sat k).mpr
  intro f hf g hg ha
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 k).mp hk
  rcases hF.2.2 k c hc with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, _, hj⟩
  · obtain ⟨hi, hj⟩ := hb.operands_l I hc hs
    obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 i (hV i hi)
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 j (hV j hj)
    exact (ssat_rel_l I hZF hF hH hc hs hE hf hx hy).trans
      (ssat_rel_l I hZF hF hJ hc hs hD hg ((ha i x hi).mp hx) ((ha j y hj).mp hy)).symm
  · obtain ⟨hi, hj⟩ := hb.operands_l I hc hs
    obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 i (hV i hi)
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 j (hV j hj)
    exact (ssat_eq_l I hZF hF hH hc hs hE hf hx hy).trans
      (ssat_eq_l I hZF hF hJ hc hs hD hg ((ha i x hi).mp hx) ((ha j y hj).mp hy)).symm
  · rw [ssat_nor_l I hZF hF hH hc hs hf, ssat_nor_l I hZF hF hJ hc hs hg]
    exact not_congr (or_congr ((sat i).mp (ih i hi) f hf g hg ha) ((sat j).mp (ih j hj) f hf g hg ha))
  · have hi := (hb.operands_l I hc hs).1
    rw [ssat_exists_l I hZF hF hH hc hs hf, ssat_exists_l I hZF hF hJ hc hs hg]
    constructor
    · rintro ⟨x, u, hx, hu, truth⟩
      obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF ((hD g).mp hg) (hW i hi) hx
      exact ⟨x, v, hx, hv, ((sat j).mp (ih j hj) u
        ((hE u).mpr (hu.function_l I ((hE f).mp hf) (hV i hi) hx)) v ((hD v).mpr hvf)
        (ha.update_l I hu hv)).mp truth⟩
    · rintro ⟨x, v, hx, hv, truth⟩
      obtain ⟨u, hu, huf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hV i hi) hx
      exact ⟨x, u, hx, hu, ((sat j).mp (ih j hj) u ((hE u).mpr huf) v
        ((hD v).mpr (hv.function_l I ((hD g).mp hg) (hW i hi) hx)) (ha.update_l I hu hv)).mpr truth⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整初等嵌入作用于有限赋值

有限参数列先延拓，再沿实际嵌入复合；有限支撑真值比较消去所选尾部。
结论量化全部内部程序，为尝试树每个节点的初等检验提供真实实例。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.finite_sat_l {ω c d A R B S j b E D F n r s t : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c A R) (hn : Smdl_d I d B S) (hj : Smap_d I ω c d A B j)
    (hb : M.mem b ω) (hF : Sfm_d I ω n F) (bound : Sbound_d I F b) (hr : M.mem r n)
    (hE : M.IsFunctionSpace I E b A) (hD : M.IsFunctionSpace I D b B)
    (hs : Fn0_d b A s) (ht : Cp0_d b A B s j t) :
    Ssat_d I A R E F n r s ↔ Ssat_d I B S D F n r t := by
  obtain ⟨a, ha⟩ := hm.2.1
  obtain ⟨f, fill, hf⟩ := senv_fill_exists_l I hZF (ω := ω) (fn0_function_l (ZF.modelsKP hZF) hs) ha
  obtain ⟨g, hg, assign⟩ := smap_assign_exists_l I hZF hj.1.1 hf
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨D₀, hD₀⟩ := ZF.exists_functionSpace hZF I ω B
  have agree : Senv_agree_d I b f s := fun i x hi => (fill.2 i x).trans
    ⟨fun h => h.2.elim And.right (fun h => (h.1 hi).elim), fun h => ⟨hω.transitive (ZF.modelsKP hZF) b hb i hi, Or.inl ⟨hi, h⟩⟩⟩
  have agree' : Senv_agree_d I b g t := by
    intro i y hi
    obtain ⟨x, hx, hix⟩ := hs.2.1 i hi
    obtain ⟨v, hv, hiv⟩ := ht.1.2.1 i hi
    have hxv := (ht.value_l hs (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1) hix).mp hiv
    have hig := assign i (hω.transitive (ZF.modelsKP hZF) b hb i hi) x v ((agree i x hi).mpr hix) hxv
    exact ⟨fun h => hg.1.2 i v y hig h ▸ hiv,
      fun h => ht.1.2.2 i hi v hv y (ht.1.bound_l h).2 hiv h ▸ hig⟩
  have left := ssat_spaces_l I hZF (R := R) hF bound hE₀ hE (hω.transitive (ZF.modelsKP hZF) b hb) (fun _ h => h)
    hr ((hE₀ f).mpr hf) ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) hs)) agree
  have right := ssat_spaces_l I hZF (R := S) hF bound hD₀ hD (hω.transitive (ZF.modelsKP hZF) b hb) (fun _ h => h)
    hr ((hD₀ g).mpr hg) ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) ht.1)) agree'
  exact left.symm.trans ((hj.ssat_l I hZF.1 hm hn hF hr hE₀ hD₀ ((hE₀ f).mpr hf) ((hD₀ g).mpr hg) assign).trans right)

end YesMetaZFC.SetTheory.Internal

/-! ## 有限求值证书的有界语法

标签与指令从原 Kuratowski 码读取，程序保持原编号。给定坐标界和实际值域界，
合法性可由 Δ₀ 公式检查，覆盖模型内部的非标准有限程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def num0_m : (k : Nat) → {n : Nat} → Term n → Formula 1 n
  | 0, _, x => Formula.forallMem x .falsum
  | k+1, _, x => Formula.existsMem x (.conj (num0_m k .newest) (KP.succ0_m x.weaken .newest))

@[simp] theorem num0_closed_l (k : Nat) {n} (x : Term n) (hx : x.freeSupport = []) : (num0_m k x).FreeClosed := by
  induction k generalizing n with
  | zero => simp -implicitDefEqProofs [num0_m, Definitional.Formula.FreeClosed, hx]
  | succ k ih => simp -implicitDefEqProofs [num0_m, Definitional.Formula.FreeClosed, hx, ih]

theorem num0_delta_l (k : Nat) {n} (x : Term n) : (num0_m k x).IsDelta0 := by
  induction k generalizing n with
  | zero => exact .forallMem _ .falsum
  | succ k ih => exact .existsMem _ (.conj (ih _) (KP.succ0_delta_l ..))

theorem num0_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (num0_m k x) ↔ Num_d k (x.eval ρ) := by
  induction k generalizing n with
  | zero => simp only [num0_m, Num_d, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff]
  | succ k ih =>
    simp only [num0_m, Num_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      ih, KP.succ0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy, hs⟩ => ⟨y, hs.predecessor_mem, hy, hs⟩⟩

def sop0_m (k : Nat) {n} (c i j : Term n) : Formula 1 n :=
  Formula.existsMem c (Formula.existsMem .newest (Formula.existsMem c.weaken.weaken
    (Formula.existsMem .newest (.conj (num0_m k .newest) (.conj
      (kpair0_m (.bound 2) i.weaken.weaken.weaken.weaken j.weaken.weaken.weaken.weaken)
      (kpair0_m c.weaken.weaken.weaken.weaken .newest (.bound 2)))))))
derive_free_closed sop0_m

theorem sop0_delta_l (k : Nat) {n} (c i j : Term n) : (sop0_m k c i j).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (num0_delta_l ..)
    (.conj (kpair0_delta_l ..) (kpair0_delta_l ..))))))

theorem sop0_sat_l (hKP : M.Models KP) (k : Nat) {n} (ρ : Env M n) (c i j : Term n) :
    Formula.satisfies ρ (sop0_m k c i j) ↔ Sop_d (kp_pair_l hKP) k (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [sop0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    num0_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine ⟨fun ⟨_, _, a, _, _, _, o, _, ho, ha, hc⟩ => ⟨a, o, ho, ha, hc⟩, ?_⟩
  rintro ⟨a, o, ho, ha, hc⟩
  obtain ⟨s, hs, has⟩ := (kpair_union_l M hc a).mpr (Or.inr rfl)
  obtain ⟨t, ht, hot⟩ := (kpair_union_l M hc o).mpr (Or.inl rfl)
  exact ⟨s, hs, a, has, t, ht, o, hot, ho, ha, hc⟩

def Fb_node_d (hKP : M.Models KP) (b r c : M.Domain) : Prop :=
  ∃ i, M.mem i b ∧ ∃ j, M.mem j b ∧
    (Sop_d (kp_pair_l hKP) 0 c i j ∨ Sop_d (kp_pair_l hKP) 1 c i j ∨
      (Sop_d (kp_pair_l hKP) 2 c i j ∧ M.mem i r ∧ M.mem j r) ∨
      (Sop_d (kp_pair_l hKP) 3 c i j ∧ M.mem j r))

def fb_node_m {n} (b r c : Term n) : Formula 1 n := Formula.existsMem b (Formula.existsMem b.weaken
  (.disj (sop0_m 0 c.weaken.weaken (.bound 1) .newest)
    (.disj (sop0_m 1 c.weaken.weaken (.bound 1) .newest)
      (.disj (.conj (sop0_m 2 c.weaken.weaken (.bound 1) .newest)
        (.conj (.mem (.bound 1) r.weaken.weaken) (.mem .newest r.weaken.weaken)))
        (.conj (sop0_m 3 c.weaken.weaken (.bound 1) .newest) (.mem .newest r.weaken.weaken))))))
derive_free_closed fb_node_m

theorem Fb_node_d.operands_l (hKP : M.Models KP) {b r c i j : M.Domain} {k : Nat}
    (h : Fb_node_d hKP b r c) (hs : Sop_d (kp_pair_l hKP) k c i j) : M.mem i b ∧ M.mem j b := by
  obtain ⟨a, ha, d, hd, code⟩ := h
  have same {l} (ht : Sop_d (kp_pair_l hKP) l c a d) : M.mem i b ∧ M.mem j b := by
    obtain ⟨_, rfl, rfl⟩ := sop_injective_l _ hKP hs ht
    exact ⟨ha, hd⟩
  rcases code with h | h | h | h
  · exact same h
  · exact same h
  · exact same h.1
  · exact same h.1

theorem fb_node_delta_l {n} (b r c : Term n) : (fb_node_m b r c).IsDelta0 :=
  .existsMem _ (.existsMem _ (.disj (sop0_delta_l ..) (.disj (sop0_delta_l ..)
    (.disj (.conj (sop0_delta_l ..) (.conj (.mem _ _) (.mem _ _))) (.conj (sop0_delta_l ..) (.mem _ _))))))

theorem fb_node_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (b r c : Term n) :
    Formula.satisfies ρ (fb_node_m b r c) ↔ Fb_node_d hKP (b.eval ρ) (r.eval ρ) (c.eval ρ) := by
  simp only [fb_node_m, Fb_node_d, Formula.satisfies_existsMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, sop0_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Fb_program_d (hKP : M.Models KP) (ω b n L F : M.Domain) : Prop :=
  M.mem b ω ∧ M.mem n ω ∧ Fn0_d n L F ∧
    ∀ r, M.mem r n → ∀ c, M.mem c L → Rd_entry_d r c F → Fb_node_d hKP b r c

def fb_program_m {n} (ω b l L F : Term n) : Formula 1 n :=
  .conj (.mem b ω) (.conj (.mem l ω) (.conj (fn0_m l L F)
    (Formula.forallMem l (Formula.forallMem L.weaken
      (.imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken) (fb_node_m b.weaken.weaken (.bound 1) .newest))))))
derive_free_closed fb_program_m

theorem fb_program_delta_l {n} (ω b l L F : Term n) : (fb_program_m ω b l L F).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (fn0_delta_l ..)
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (fb_node_delta_l ..))))))

theorem fb_program_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (ω b l L F : Term n) :
    Formula.satisfies ρ (fb_program_m ω b l L F) ↔
      Fb_program_d hKP (ω.eval ρ) (b.eval ρ) (l.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [fb_program_m, Fb_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hKP.1, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, fb_node_sat_l hKP, Definitional.Term.eval_weaken]; rfl

theorem fb_program_of_l (hKP : M.Models KP) {ω b n L F : M.Domain}
    (hF : Sfm_d (kp_pair_l hKP) ω n F) (hb : M.mem b ω) (bound : Sbound_d (kp_pair_l hKP) F b)
    (hf : Fn0_d n L F) : Fb_program_d hKP ω b n L F := by
  refine ⟨hb, hF.1, hf, fun r _ c _ hc => ?_⟩
  rcases hF.2.2 r c hc with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, _, hj⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inl hs⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inr (Or.inl hs)⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inr (Or.inr (Or.inl ⟨hs, hi, hj⟩))⟩
  · exact ⟨i, (bound.operands_l _ hc hs).1, j, (bound.operands_l _ hc hs).2, Or.inr (Or.inr (Or.inr ⟨hs, hj⟩))⟩

theorem Fb_program_d.read_l (hZF : M.Models ZF) {ω b n L F : M.Domain} (hω : M.IsOmega ω)
    (h : Fb_program_d (ZF.modelsKP hZF) ω b n L F) : Sfm_d (kp_pair_l (ZF.modelsKP hZF)) ω n F ∧
      Sbound_d (kp_pair_l (ZF.modelsKP hZF)) F b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have row r c (hc : Rd_entry_d r c F) := h.2.2.2 r (h.2.2.1.bound_l hc).1 c (h.2.2.1.bound_l hc).2 hc
  refine ⟨⟨h.2.1, ⟨(hω.isOrdinal (ZF.modelsKP hZF)).mem h.2.1, (fn0_function_l (ZF.modelsKP hZF) h.2.2.1).1,
    (fn0_function_l (ZF.modelsKP hZF) h.2.2.1).2.1⟩, fun r c hc => ?_⟩, fun r i j coord => ?_⟩
  · obtain ⟨i, hi, j, hj, hs | hs | hs | hs⟩ := row r c hc
    · exact Or.inl ⟨i, j, hs, hω.transitive (ZF.modelsKP hZF) b h.1 i hi, hω.transitive (ZF.modelsKP hZF) b h.1 j hj⟩
    · exact Or.inr (Or.inl ⟨i, j, hs, hω.transitive (ZF.modelsKP hZF) b h.1 i hi, hω.transitive (ZF.modelsKP hZF) b h.1 j hj⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, j, hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, j, hs.1, hω.transitive (ZF.modelsKP hZF) b h.1 i hi, hs.2⟩))
  · obtain ⟨c, o, a, hc, hco, ha⟩ := coord
    have finish {k i' j'} (hi : M.mem i' b) (hj : M.mem j' b) (hs : Sop_d I k c i' j') :
        M.mem i b ∧ M.mem j b := by
      obtain ⟨a', o', _, ha', hc'⟩ := hs
      obtain ⟨_, e⟩ := I.injective hco hc'
      obtain ⟨rfl, rfl⟩ := I.injective ha (e.symm ▸ ha')
      exact ⟨hi, hj⟩
    obtain ⟨i', hi, j', hj, hs | hs | hs | hs⟩ := row r c hc
    · exact finish hi hj hs
    · exact finish hi hj hs
    · exact finish hi hj hs.1
    · exact finish hi hj hs.1

end YesMetaZFC.SetTheory.Internal

/-! ## 有限真值表的 Δ₀ 检验证书

量词只遍历有限赋值空间、对象域和已有真值集。表仍解释原四种指令，
并明确保留全部行的函数图、值域界及 Tarski 方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Se_update0_d (b A f i x g : M.Domain) : Prop := Fn0_d b A g ∧
  ∀ j, M.mem j b → ∀ y, M.mem y A →
    (Rd_entry_d j y g ↔ (j = i ∧ y = x) ∨ (j ≠ i ∧ Rd_entry_d j y f))

def se_update0_m {n} (b A f i x g : Term n) : Formula 1 n := .conj (fn0_m b A g)
  (Formula.forallMem b (Formula.forallMem A.weaken (.iff
    (rd_entry0_m (.bound 1) .newest g.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken) (Formula.extensionalEq .newest x.weaken.weaken))
      (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken)) (rd_entry0_m (.bound 1) .newest f.weaken.weaken))))))
derive_free_closed se_update0_m

theorem se_update0_delta_l {n} (b A f i x g : Term n) : (se_update0_m b A f i x g).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..)
    (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (.conj (.neg (.atom _ _ _)) (rd_entry0_delta_l ..))))))

theorem se_update0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b A f i x g : Term n) :
    Formula.satisfies ρ (se_update0_m b A f i x g) ↔
      Se_update0_d (b.eval ρ) (A.eval ρ) (f.eval ρ) (i.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [se_update0_m, Se_update0_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hE,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

theorem se_update0_l (hKP : M.Models KP) {b A f i x g : M.Domain}
    (hf : Fn0_d b A f) (hi : M.mem i b) (hx : M.mem x A) :
    Se_update0_d b A f i x g ↔ Senv_update_d (kp_pair_l hKP) f i x g := by
  refine ⟨fun ⟨hg, h⟩ => ⟨(fn0_function_l hKP hg).1.1, fun j y => ⟨?_, ?_⟩⟩, fun h => ?_⟩
  · intro hjy
    exact (h j (hg.bound_l hjy).1 y (hg.bound_l hjy).2).mp hjy
  · intro hy
    have bound : M.mem j b ∧ M.mem y A := hy.elim (fun ⟨rfl, rfl⟩ => ⟨hi, hx⟩) (fun h => hf.bound_l h.2)
    exact (h j bound.1 y bound.2).mpr hy
  · exact ⟨fn0_of_function_l hKP (h.function_l _ (fn0_function_l hKP hf) hi hx), fun j _ y _ => h.2 j y⟩

def Fv_arg_d (k : Nat) (b A R E C H f i j : M.Domain) : Prop := match k with
  | 0 => ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧ Rd_entry_d i x f ∧ Rd_entry_d j y f ∧ Rd_entry_d x y R
  | 1 => ∃ x, M.mem x A ∧ Rd_entry_d i x f ∧ Rd_entry_d j x f
  | 2 => ∃ Y, M.mem Y C ∧ ∃ Z, M.mem Z C ∧ Rd_entry_d i Y H ∧ Rd_entry_d j Z H ∧ ¬ (M.mem f Y ∨ M.mem f Z)
  | _ => ∃ Y, M.mem Y C ∧ Rd_entry_d j Y H ∧ ∃ x, M.mem x A ∧ ∃ g, M.mem g E ∧ Se_update0_d b A f i x g ∧ M.mem g Y

def fv_arg_m (k : Nat) {n} (b A R E C H f i j : Term n) : Formula 1 n := match k with
  | 0 => Formula.existsMem A (Formula.existsMem A.weaken (.conj
      (rd_entry0_m i.weaken.weaken (.bound 1) f.weaken.weaken) (.conj
        (rd_entry0_m j.weaken.weaken .newest f.weaken.weaken) (rd_entry0_m (.bound 1) .newest R.weaken.weaken))))
  | 1 => Formula.existsMem A (.conj (rd_entry0_m i.weaken .newest f.weaken) (rd_entry0_m j.weaken .newest f.weaken))
  | 2 => Formula.existsMem C (Formula.existsMem C.weaken (.conj
      (rd_entry0_m i.weaken.weaken (.bound 1) H.weaken.weaken) (.conj
        (rd_entry0_m j.weaken.weaken .newest H.weaken.weaken) (.neg (.disj (.mem f.weaken.weaken (.bound 1)) (.mem f.weaken.weaken .newest))))))
  | _ => Formula.existsMem C (.conj (rd_entry0_m j.weaken .newest H.weaken)
      (Formula.existsMem A.weaken (Formula.existsMem E.weaken.weaken (.conj
        (se_update0_m b.weaken.weaken.weaken A.weaken.weaken.weaken f.weaken.weaken.weaken
          i.weaken.weaken.weaken (.bound 1) .newest) (.mem .newest (.bound 2))))))

@[simp] theorem fv_arg_closed_l (k : Nat) {n} (b A R E C H f i j : Term n)
    (hb : b.freeSupport = []) (hA : A.freeSupport = []) (hR : R.freeSupport = []) (hE : E.freeSupport = [])
    (hC : C.freeSupport = []) (hH : H.freeSupport = []) (hf : f.freeSupport = [])
    (hi : i.freeSupport = []) (hj : j.freeSupport = []) : (fv_arg_m k b A R E C H f i j).FreeClosed := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp -implicitDefEqProofs [fv_arg_m, Definitional.Formula.FreeClosed, hb, hA, hR, hE, hC, hH, hf, hi, hj]

theorem fv_arg_delta_l (k : Nat) {n} (b A R E C H f i j : Term n) : (fv_arg_m k b A R E C H f i j).IsDelta0 := by
  rcases k with _ | (_ | (_ | k))
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
  · exact .existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.neg (.disj (.mem _ _) (.mem _ _))))))
  · exact .existsMem _ (.conj (rd_entry0_delta_l ..) (.existsMem _ (.existsMem _ (.conj (se_update0_delta_l ..) (.mem _ _)))))

theorem fv_arg_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (b A R E C H f i j : Term n) :
    Formula.satisfies ρ (fv_arg_m k b A R E C H f i j) ↔
      Fv_arg_d k (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (C.eval ρ) (H.eval ρ) (f.eval ρ) (i.eval ρ) (j.eval ρ) := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp only [fv_arg_m, Fv_arg_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hE, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      se_update0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def Fv_node_d (hKP : M.Models KP) (b A R E C H c f : M.Domain) : Prop :=
  ∃ k : Fin 4, ∃ i, M.mem i b ∧ ∃ j, M.mem j b ∧
    Sop_d (kp_pair_l hKP) k.val c i j ∧ Fv_arg_d k.val b A R E C H f i j

private def fv_case_m (k : Nat) {n} (b A R E C H c f : Term n) : Formula 1 n :=
  Formula.existsMem b (Formula.existsMem b.weaken (.conj (sop0_m k c.weaken.weaken (.bound 1) .newest)
    (fv_arg_m k b.weaken.weaken A.weaken.weaken R.weaken.weaken E.weaken.weaken C.weaken.weaken
      H.weaken.weaken f.weaken.weaken (.bound 1) .newest)))
derive_free_closed fv_case_m

def fv_node_m {n} (b A R E C H c f : Term n) : Formula 1 n :=
  .disj (fv_case_m 0 b A R E C H c f) (.disj (fv_case_m 1 b A R E C H c f)
    (.disj (fv_case_m 2 b A R E C H c f) (fv_case_m 3 b A R E C H c f)))
derive_free_closed fv_node_m

theorem fv_node_delta_l {n} (b A R E C H c f : Term n) : (fv_node_m b A R E C H c f).IsDelta0 := by
  have h k : (fv_case_m k b A R E C H c f).IsDelta0 :=
    .existsMem _ (.existsMem _ (.conj (sop0_delta_l ..) (fv_arg_delta_l ..)))
  exact .disj (h 0) (.disj (h 1) (.disj (h 2) (h 3)))

theorem fv_node_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (b A R E C H c f : Term n) :
    Formula.satisfies ρ (fv_node_m b A R E C H c f) ↔
      Fv_node_d hKP (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (C.eval ρ) (H.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [fv_node_m, Fv_node_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, fv_case_m,
    Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    sop0_sat_l hKP, fv_arg_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Fv_eval_d (hKP : M.Models KP) (b A R E n L F C H : M.Domain) : Prop := Fn0_d n C H ∧
  ∀ r, M.mem r n → ∀ c, M.mem c L → ∀ Y, M.mem Y C → Rd_entry_d r c F → Rd_entry_d r Y H →
    M.MemberSubset Y E ∧ ∀ f, M.mem f E → (M.mem f Y ↔ Fv_node_d hKP b A R E C H c f)

def fv_eval_m {d} (b A R E n L F C H : Term d) : Formula 1 d := .conj (fn0_m n C H)
  (Formula.forallMem n (Formula.forallMem L.weaken (Formula.forallMem C.weaken.weaken (.imp
    (rd_entry0_m (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.imp
      (rd_entry0_m (.bound 2) .newest H.weaken.weaken.weaken) (.conj (Formula.subset .newest E.weaken.weaken.weaken)
        (Formula.forallMem E.weaken.weaken.weaken (.iff (.mem .newest (.bound 1))
          (fv_node_m b.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            E.weaken.weaken.weaken.weaken C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 2) .newest)))))))))
derive_free_closed fv_eval_m

theorem fv_eval_delta_l {d} (b A R E n L F C H : Term d) : (fv_eval_m b A R E n L F C H).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.imp (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (fv_node_delta_l ..)))))))))

theorem fv_eval_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (b A R E n L F C H : Term d) :
    Formula.satisfies ρ (fv_eval_m b A R E n L F C H) ↔ Fv_eval_d hKP
      (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (C.eval ρ) (H.eval ρ) := by
  simp only [fv_eval_m, Fv_eval_d, Formula.satisfies_conj_iff, fn0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    Formula.satisfies_subset_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fv_node_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

/-- 用已有全部有限列作界，精确检查某一长度的赋值空间。 -/
def Fv_space_d (b A J E : M.Domain) : Prop := M.MemberSubset E J ∧
  ∀ f, M.mem f J → (M.mem f E ↔ Fn0_d b A f)

def fv_space_m {n} (b A J E : Term n) : Formula 1 n := .conj (Formula.subset E J)
  (Formula.forallMem J (.iff (.mem .newest E.weaken) (fn0_m b.weaken A.weaken .newest)))
derive_free_closed fv_space_m

theorem fv_space_delta_l {n} (b A J E : Term n) : (fv_space_m b A J E).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (fn0_delta_l ..)))

theorem fv_space_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b A J E : Term n) :
    Formula.satisfies ρ (fv_space_m b A J E) ↔ Fv_space_d (b.eval ρ) (A.eval ρ) (J.eval ρ) (E.eval ρ) := by
  simp only [fv_space_m, Fv_space_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Fv_at_d (C H r f : M.Domain) : Prop := ∃ Y, M.mem Y C ∧ Rd_entry_d r Y H ∧ M.mem f Y

def fv_at_m {n} (C H r f : Term n) : Formula 1 n := Formula.existsMem C
  (.conj (rd_entry0_m r.weaken .newest H.weaken) (.mem f.weaken .newest))
derive_free_closed fv_at_m

theorem fv_at_delta_l {n} (C H r f : Term n) : (fv_at_m C H r f).IsDelta0 :=
  .existsMem _ (.conj (rd_entry0_delta_l ..) (.mem _ _))

theorem fv_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C H r f : Term n) :
    Formula.satisfies ρ (fv_at_m C H r f) ↔ Fv_at_d (C.eval ρ) (H.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [fv_at_m, Fv_at_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 有限真值证书与原满足关系的双向对应

有界证书精确恢复原递归图；它不是一份额外假定正确的真值表。
合法程序在有限赋值空间上的实际求值给出证书，证书也唯一决定所有行。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem fv_arg_l (hKP : M.Models KP) {b A R E n C H f i j : M.Domain}
    (hE : M.IsFunctionSpace (kp_pair_l hKP) E b A) (hf : M.mem f E) (hi : M.mem i b)
    (hH : Fn0_d n C H) (rows : ∀ r Y, Rd_entry_d r Y H → M.MemberSubset Y E) (k : Nat) :
    Fv_arg_d k b A R E C H f i j ↔ Sarg_d (kp_pair_l hKP) k A R H f i j := by
  have fn := (hE f).mp hf
  rcases k with _ | (_ | (_ | k))
  · exact ⟨fun ⟨x, _, y, _, hx, hy, h⟩ => ⟨x, y, hx, hy, h⟩,
      fun ⟨x, y, hx, hy, h⟩ => ⟨x, fn.output_mem_of_pairMember hx, y, fn.output_mem_of_pairMember hy, hx, hy, h⟩⟩
  · exact ⟨fun ⟨x, _, hx, hy⟩ => ⟨x, hx, hy⟩,
      fun ⟨x, hx, hy⟩ => ⟨x, fn.output_mem_of_pairMember hx, hx, hy⟩⟩
  · exact ⟨fun ⟨Y, _, Z, _, hY, hZ, h⟩ => ⟨Y, Z, hY, hZ, h⟩,
      fun ⟨Y, Z, hY, hZ, h⟩ => ⟨Y, (hH.bound_l hY).2, Z, (hH.bound_l hZ).2, hY, hZ, h⟩⟩
  · exact ⟨fun ⟨Y, _, hY, x, hx, g, _, hg, h⟩ =>
      ⟨Y, hY, x, g, hx, (se_update0_l hKP (fn0_of_function_l hKP fn) hi hx).mp hg, h⟩,
      fun ⟨Y, hY, x, g, hx, hg, h⟩ => ⟨Y, (hH.bound_l hY).2, hY, x, hx, g, rows j Y hY g h,
        (se_update0_l hKP (fn0_of_function_l hKP fn) hi hx).mpr hg, h⟩⟩

theorem fv_node_l (hKP : M.Models KP) {b A R E n C H c f r : M.Domain}
    (hE : M.IsFunctionSpace (kp_pair_l hKP) E b A) (hf : M.mem f E) (hc : Fb_node_d hKP b r c)
    (hH : Fn0_d n C H) (rows : ∀ r Y, Rd_entry_d r Y H → M.MemberSubset Y E) :
    Fv_node_d hKP b A R E C H c f ↔ Snode_d (kp_pair_l hKP) A R H c f := by
  refine ⟨fun ⟨k, i, hi, j, _, hs, h⟩ => ⟨k, i, j, hs, (fv_arg_l hKP hE hf hi hH rows k.val).mp h⟩, ?_⟩
  rintro ⟨k, i, j, hs, h⟩
  obtain ⟨hi, hj⟩ := hc.operands_l hKP hs
  exact ⟨k, i, hi, j, hj, hs, (fv_arg_l hKP hE hf hi hH rows k.val).mpr h⟩

theorem fv_eval_of_l (hZF : M.Models ZF) {ω b A R E n L F C H : M.Domain}
    (hω : M.IsOmega ω) (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E b A)
    (hH : Seval_d (kp_pair_l (ZF.modelsKP hZF)) A R E F n H) (fn : Fn0_d n C H) :
    Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hF := (program.read_l hZF hω).1
  have rows r Y (hY : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp (fn.bound_l hY).1
    exact fun f hf => ((seval_row_l I hZF hF hH hc hY f).mp hf).1
  refine ⟨fn, fun r hr c hc Y _ hrc hrY => ⟨rows r Y hrY, fun f hf => ?_⟩⟩
  exact (seval_row_l I hZF hF hH hrc hrY f).trans ((and_iff_right hf).trans
    (fv_node_l (ZF.modelsKP hZF) hE hf (program.2.2.2 r hr c hc hrc) fn rows).symm)

theorem Fv_eval_d.seval_l (hZF : M.Models ZF) {ω b A R E n L F C H : M.Domain}
    (hω : M.IsOmega ω) (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E b A)
    (h : Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H) :
    Seval_d (kp_pair_l (ZF.modelsKP hZF)) A R E F n H := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hF := (program.read_l hZF hω).1
  have rows r Y (hY : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨c, hc, hrc⟩ := program.2.2.1.2.1 r (h.1.bound_l hY).1
    exact (h.2 r (h.1.bound_l hY).1 c hc Y (h.1.bound_l hY).2 hrc hY).1
  have fn := fn0_function_l (ZF.modelsKP hZF) h.1
  refine ⟨⟨hF.2.1.1, fn.1, fn.2.1⟩, fun r hr Y hrY => ?_⟩
  obtain ⟨c, hc, hrc⟩ := program.2.2.1.2.1 r hr
  obtain ⟨P, hP⟩ := ZF.exists_restriction hZF I H r
  have dom := (hP.isSetFunctionFromTo fn (hF.2.1.1.transitive r hr)).2.1
  have node := h.2 r hr c hc Y (h.1.bound_l hrY).2 hrc hrY
  refine ⟨P, hP, fun f => ?_⟩
  have read : M.mem f Y ↔ M.mem f E ∧ Snode_d I A R H c f :=
    ⟨fun hf => ⟨node.1 f hf, (fv_node_l (ZF.modelsKP hZF) hE (node.1 f hf)
      (program.2.2.2 r hr c hc hrc) h.1 rows).mp ((node.2 f (node.1 f hf)).mp hf)⟩,
      fun ⟨hf, ht⟩ => (node.2 f hf).mpr ((fv_node_l (ZF.modelsKP hZF) hE hf
        (program.2.2.2 r hr c hc hrc) h.1 rows).mpr ht)⟩
  apply read.trans
  apply and_congr_right
  intro _
  refine ⟨fun ht => ⟨r, c, dom, hrc, (snode_restrict_l I (ZF.modelsKP hZF) (hF.2.2 r c hrc) hP f).mpr ht⟩, ?_⟩
  rintro ⟨k, d, hd, hkd, ht⟩
  have eq := hd.eq hZF.1 dom
  subst k
  have eq := hF.2.1.2.1.2 r d c hkd hrc
  subst d
  exact (snode_restrict_l I (ZF.modelsKP hZF) (hF.2.2 r c hrc) hP f).mp ht

theorem fv_space_l (hKP : M.Models KP) {ω b A J E : M.Domain} (hb : M.mem b ω)
    (hJ : Fseq_space_d (kp_pair_l hKP) ω A J) : Fv_space_d b A J E ↔ M.IsFunctionSpace (kp_pair_l hKP) E b A := by
  refine ⟨fun h f => ⟨fun hf => fn0_function_l hKP ((h.2 f (h.1 f hf)).mp hf), fun hf =>
    (h.2 f ((hJ f).mpr ⟨b, hb, hf⟩)).mpr (fn0_of_function_l hKP hf)⟩, fun h => ⟨?_, ?_⟩⟩
  · exact fun f hf => (hJ f).mpr ⟨b, hb, (h f).mp hf⟩
  · exact fun f _ => (h f).trans ⟨fn0_of_function_l hKP, fn0_function_l hKP⟩

theorem Fv_eval_d.truth_l (hZF : M.Models ZF) {ω b A R E n L F C H r f : M.Domain}
    (hω : M.IsOmega ω) (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E b A)
    (h : Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H) (hr : M.mem r n) :
    Fv_at_d C H r f ↔ Ssat_d (kp_pair_l (ZF.modelsKP hZF)) A R E F n r f := by
  obtain ⟨Y, hY, hrY⟩ := h.1.2.1 r hr
  refine Iff.trans ?_ (ssat_value_l _ hZF (h.seval_l hZF hω program hE) hrY f).symm
  exact ⟨fun ⟨Y', hY', hrY', hf⟩ => h.1.2.2 r hr Y' hY' Y hY hrY' hrY ▸ hf,
    fun hf => ⟨Y, hY, hrY, hf⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## Skolem 见证的有限真值证书

只记录更新后赋值在程序支撑上的值。参数列长度和被更新坐标不必落在该
支撑内，因此同一证书覆盖全部内部公式及全部有限参数列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Fw_env_d (b A u n s i x t : M.Domain) : Prop := Fn0_d b A t ∧
  ∀ v, M.mem v b → ∀ y, M.mem y A → (Rd_entry_d v y t ↔
    (v = i ∧ y = x) ∨ (v ≠ i ∧ ((M.mem v n ∧ Rd_entry_d v y s) ∨ (¬ M.mem v n ∧ y = u))))

def fw_env_m {d} (b A u n s i x t : Term d) : Formula 1 d := .conj (fn0_m b A t)
  (Formula.forallMem b (Formula.forallMem A.weaken (.iff (rd_entry0_m (.bound 1) .newest t.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken) (Formula.extensionalEq .newest x.weaken.weaken))
      (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken))
        (.disj (.conj (.mem (.bound 1) n.weaken.weaken) (rd_entry0_m (.bound 1) .newest s.weaken.weaken))
          (.conj (.neg (.mem (.bound 1) n.weaken.weaken)) (Formula.extensionalEq .newest u.weaken.weaken))))))))
derive_free_closed fw_env_m

theorem fw_env_delta_l {d} (b A u n s i x t : Term d) : (fw_env_m b A u n s i x t).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..)
    (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (.conj (.neg (.atom _ _ _))
      (.disj (.conj (.mem _ _) (rd_entry0_delta_l ..)) (.conj (.neg (.mem _ _)) (.atom _ _ _))))))))

theorem fw_env_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b A u n s i x t : Term d) :
    Formula.satisfies ρ (fw_env_m b A u n s i x t) ↔ Fw_env_d
      (b.eval ρ) (A.eval ρ) (u.eval ρ) (n.eval ρ) (s.eval ρ) (i.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [fw_env_m, Fw_env_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hE, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]; rfl

theorem fw_env_read_l (hKP : M.Models KP) {ω b A u n s i x t f g : M.Domain}
    (hb : M.MemberSubset b ω) (hf : Senv_fill_d (kp_pair_l hKP) ω u n s f)
    (hg : Senv_update_d (kp_pair_l hKP) f i x g) (hG : M.IsSetFunctionFromTo (kp_pair_l hKP) g ω A)
    (ht : Fn0_d b A t) : Fw_env_d b A u n s i x t ↔ Senv_agree_d (kp_pair_l hKP) b g t := by
  have value v y (hv : M.mem v b) := (hg.2 v y).trans (or_congr Iff.rfl
    (and_congr Iff.rfl ((hf.2 v y).trans (and_iff_right (hb v hv)))))
  exact ⟨fun h v y hv => ⟨fun hgy => (h.2 v hv y (hG.output_mem_of_pairMember hgy)).mpr ((value v y hv).mp hgy),
    fun hty => (value v y hv).mpr ((h.2 v hv y (ht.bound_l hty).2).mp hty)⟩,
    fun h => ⟨ht, fun v hv y _ => (h v y hv).symm.trans (value v y hv)⟩⟩

def Fw_cert_d (hKP : M.Models KP) (ω A R J u a i s x n b l L F E C H t r : M.Domain) : Prop :=
  M.mem n ω ∧ Fn0_d n A s ∧ KPair_d M a F r ∧ M.mem r l ∧ Fb_program_d hKP ω b l L F ∧
    Fv_space_d b A J E ∧ Fv_eval_d hKP b A R E l L F C H ∧ Fw_env_d b A u n s i x t ∧ Fv_at_d C H r t

def fw_cert_m {d} (ω A R J u a i s x n b l L F E C H t r : Term d) : Formula 1 d :=
  .conj (.mem n ω) (.conj (fn0_m n A s) (.conj (kpair0_m a F r) (.conj (.mem r l)
    (.conj (fb_program_m ω b l L F) (.conj (fv_space_m b A J E) (.conj (fv_eval_m b A R E l L F C H)
      (.conj (fw_env_m b A u n s i x t) (fv_at_m C H r t))))))))
derive_free_closed fw_cert_m

theorem fw_cert_delta_l {d} (ω A R J u a i s x n b l L F E C H t r : Term d) :
    (fw_cert_m ω A R J u a i s x n b l L F E C H t r).IsDelta0 :=
  .conj (.mem _ _) (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (.mem _ _)
    (.conj (fb_program_delta_l ..) (.conj (fv_space_delta_l ..) (.conj (fv_eval_delta_l ..)
      (.conj (fw_env_delta_l ..) (fv_at_delta_l ..))))))))

theorem fw_cert_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A R J u a i s x n b l L F E C H t r : Term d) :
    Formula.satisfies ρ (fw_cert_m ω A R J u a i s x n b l L F E C H t r) ↔ Fw_cert_d hKP
      (ω.eval ρ) (A.eval ρ) (R.eval ρ) (J.eval ρ) (u.eval ρ) (a.eval ρ) (i.eval ρ) (s.eval ρ) (x.eval ρ)
      (n.eval ρ) (b.eval ρ) (l.eval ρ) (L.eval ρ) (F.eval ρ) (E.eval ρ) (C.eval ρ) (H.eval ρ) (t.eval ρ) (r.eval ρ) := by
  simp only [fw_cert_m, Fw_cert_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hKP.1, kpair0_sat_l hKP.1, fb_program_sat_l hKP, fv_space_sat_l hKP.1,
    fv_eval_sat_l hKP, fw_env_sat_l hKP.1, fv_at_sat_l hKP.1]

def fw_witness_m {d} (ω A R J u a i s x : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (fw_cert_m (w ω) (w A) (w R) (w J) (w u) (w a) (w i) (w s) (w x)
      (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed fw_witness_m

theorem Fw_cert_d.witness_l (hZF : M.Models ZF) {ω c A R J u a i s x n b l L F E C H t r : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c A R)
    (hJ : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A J) (hu : M.mem u A) (hi : M.mem i ω) (hx : M.mem x A)
    (h : Fw_cert_d (ZF.modelsKP hZF) ω A R J u a i s x n b l L F E C H t r) :
    Ssk_wit_d (kp_pair_l (ZF.modelsKP hZF)) ω c A u a i s x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hn, hs, code, hr, program, space, ev, env, ht⟩ := h
  obtain ⟨hF, bound⟩ := program.read_l hZF hω
  have hE := (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mp space
  obtain ⟨f, hf, fn⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) hs) hu
  obtain ⟨g, hg, gn⟩ := senv_update_exists_l I hZF fn hi hx
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
  have same := ssat_spaces_l I hZF (R := R) hF bound hE₀ hE (hω.transitive (ZF.modelsKP hZF) b program.1) (fun _ h => h) hr
    ((hE₀ g).mpr gn) ((hE t).mpr (fn0_function_l (ZF.modelsKP hZF) env.1))
    ((fw_env_read_l (ZF.modelsKP hZF) (hω.transitive (ZF.modelsKP hZF) b program.1) hf hg gn env.1).mp env)
  exact ⟨n, f, g, hn, fn0_function_l (ZF.modelsKP hZF) hs, hf, hg,
    (satisfies_decode_l I hZF.1 hm ⟨code, hF, hr⟩ hE₀).mpr (same.mpr ((ev.truth_l hZF hω program hE hr).mp ht))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 小 Skolem 壳的有界结构数据

运算闭性只检查已有的有限参数空间与选择图。枚举是实际双射图；其
有界公式能在传递源与背景之间直接读取，不诉诸外部基数正确性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sh_product_m {d} (P A B : Term d) : Formula 1 d :=
  .conj (Formula.forallMem P (Formula.existsMem A.weaken (Formula.existsMem B.weaken.weaken
    (kpair0_m (.bound 2) (.bound 1) .newest))))
    (Formula.forallMem A (Formula.forallMem B.weaken (Formula.existsMem P.weaken.weaken
      (kpair0_m .newest (.bound 2) (.bound 1)))))
derive_free_closed sh_product_m

theorem sh_product_delta_l {d} (P A B : Term d) : (sh_product_m P A B).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.existsMem _ (kpair0_delta_l ..))))

theorem sh_product_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (P A B : Term d) :
    Formula.satisfies ρ (sh_product_m P A B) ↔
      M.IsCartesianProduct (kp_pair_l hKP) (P.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [sh_product_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken]
  refine ⟨fun h p => ⟨h.1 p, ?_⟩, fun h => ⟨fun p hp => (h p).mp hp, ?_⟩⟩
  · rintro ⟨a, ha, b, hb, hp⟩
    obtain ⟨q, hq, code⟩ := h.2 a ha b hb
    exact kpair_unique_l M hKP.1 code hp ▸ hq
  · intro a ha b hb
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total a b
    exact ⟨p, (h p).mpr ⟨a, ha, b, hb, hp⟩, hp⟩

def sh_bijection_m {d} (f A B : Term d) : Formula 1 d := .conj (fn0_m A B f)
  (.conj (Formula.forallMem A (Formula.forallMem A.weaken (Formula.forallMem B.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken)
        (Formula.extensionalEq (.bound 2) (.bound 1)))))))
    (Formula.forallMem B (Formula.existsMem A.weaken (rd_entry0_m .newest (.bound 1) f.weaken.weaken))))
derive_free_closed sh_bijection_m

theorem sh_bijection_delta_l {d} (f A B : Term d) : (sh_bijection_m f A B).IsDelta0 :=
  .conj (fn0_delta_l ..) (.conj (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom _ _ _))))))
    (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..))))

theorem sh_bijection_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (f A B : Term d) :
    Formula.satisfies ρ (sh_bijection_m f A B) ↔
      M.IsSetBijectionFromTo (kp_pair_l hKP) (f.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [sh_bijection_m, Formula.satisfies_conj_iff, fn0_sat_l hKP.1, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1,
    Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hf, hi, ho⟩ => ⟨⟨fn0_function_l hKP hf,
    fun a b x ha hb => hi a (hf.bound_l ha).1 b (hf.bound_l hb).1 x (hf.bound_l ha).2 ha hb⟩, ho⟩,
    fun hf => ⟨fn0_of_function_l hKP hf.1.1, fun a _ b _ x _ => hf.1.2 a b x, hf.2⟩⟩

def sh_value_m {d} (ω J T D K B x : Term d) : Formula 1 d :=
  Formula.existsMem ω (Formula.existsMem J.weaken (Formula.existsMem T.weaken.weaken
    (Formula.existsMem D.weaken.weaken.weaken (.conj
      (fn0_m (.bound 3) B.weaken.weaken.weaken.weaken (.bound 2)) (.conj
      (kpair0_m .newest (.bound 1) (.bound 2))
      (rd_entry0_m .newest x.weaken.weaken.weaken.weaken K.weaken.weaken.weaken.weaken))))))
derive_free_closed sh_value_m

theorem sh_value_delta_l {d} (ω J T D K B x : Term d) : (sh_value_m ω J T D K B x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))))

theorem sh_value_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω J T D K B x : Term d) :
    Formula.satisfies ρ (sh_value_m ω J T D K B x) ↔
      ∃ n, M.mem n (ω.eval ρ) ∧ ∃ s, M.mem s (J.eval ρ) ∧ ∃ t, M.mem t (T.eval ρ) ∧
        ∃ p, M.mem p (D.eval ρ) ∧ Fn0_d n (B.eval ρ) s ∧ KPair_d M p t s ∧ Rd_entry_d p (x.eval ρ) (K.eval ρ) := by
  simp only [sh_value_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

def sh_closed_m {d} (ω A J T D K B : Term d) : Formula 1 d := Formula.forallMem A
  (.imp (sh_value_m ω.weaken J.weaken T.weaken D.weaken K.weaken B.weaken .newest) (.mem .newest B.weaken))
derive_free_closed sh_closed_m

theorem sh_closed_delta_l {d} (ω A J T D K B : Term d) : (sh_closed_m ω A J T D K B).IsDelta0 :=
  .forallMem _ (.imp (sh_value_delta_l ..) (.mem _ _))

theorem sh_closed_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A J T D K B : Term d)
    (hJ : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (A.eval ρ) (J.eval ρ))
    (hD : M.IsCartesianProduct (kp_pair_l hKP) (D.eval ρ) (T.eval ρ) (J.eval ρ))
    (hK : M.IsSetFunctionFromTo (kp_pair_l hKP) (K.eval ρ) (D.eval ρ) (A.eval ρ))
    (hB : M.MemberSubset (B.eval ρ) (A.eval ρ)) :
    Formula.satisfies ρ (sh_closed_m ω A J T D K B) ↔
      Fc_closed_d (kp_pair_l hKP) (ω.eval ρ) (T.eval ρ) (K.eval ρ) (B.eval ρ) := by
  simp only [sh_closed_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    sh_value_sat_l hKP, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  refine ⟨fun h x hx => ?_, fun h x _ ⟨n, hn, s, _, t, ht, p, _, hs, hp, hx⟩ =>
    h x ⟨n, s, t, p, hn, fn0_function_l hKP hs, ht, hp, hx⟩⟩
  obtain ⟨n, s, t, p, hn, hs, ht, hp, hx⟩ := hx
  have hsJ := (hJ s).mpr ⟨n, hn, hs.mono_target_l _ hB⟩
  exact h x (hK.output_mem_of_pairMember hx)
    ⟨n, hn, s, hsJ, t, ht, p, (hD p).mpr ⟨t, ht, s, hsJ, hp⟩, fn0_of_function_l hKP hs, hp, hx⟩

def sh_codes_m {d} (ω C : Term d) : Formula 1 d := .forallE (.iff (.mem .newest C.weaken)
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (fb_program_m ω.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (.conj (.mem .newest (.bound 3)) (kpair0_m (.bound 5) (.bound 1) .newest)))))))))
derive_free_closed sh_codes_m

def sh_sequences_m {d} (ω A J : Term d) : Formula 1 d := .forallE (.iff (.mem .newest J.weaken)
  (Formula.existsMem ω.weaken (fn0_m .newest A.weaken.weaken (.bound 1))))
derive_free_closed sh_sequences_m

def sh_choice_m {d} (ω A R J u a i s x : Term d) : Formula 1 d :=
  .disj (fw_witness_m ω A R J u a i s x)
    (.conj (Formula.forallMem A (.neg (fw_witness_m ω.weaken A.weaken R.weaken J.weaken
      u.weaken a.weaken i.weaken s.weaken .newest))) (Formula.extensionalEq x u))
derive_free_closed sh_choice_m

def sh_select_m {d} (ω A R u C J T D K : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken
  Formula.forallMem C (Formula.forallMem ω.weaken (Formula.forallMem T.weaken.weaken
    (Formula.forallMem J.weaken.weaken.weaken (Formula.forallMem D.weaken.weaken.weaken.weaken
      (Formula.forallMem A.weaken.weaken.weaken.weaken.weaken
        (.imp (kpair0_m (.bound 3) (.bound 5) (.bound 4)) (.imp (kpair0_m (.bound 1) (.bound 3) (.bound 2))
          (.imp (rd_entry0_m (.bound 1) .newest (w K))
            (sh_choice_m (w ω) (w A) (w R) (w J) (w u) (.bound 5) (.bound 4) (.bound 2) .newest)))))))))
derive_free_closed sh_select_m

def sh_skolem_m {d} (ω A R u C J T D K : Term d) : Formula 1 d :=
  .conj (.mem u A) (.conj (sh_codes_m ω C) (.conj (sh_sequences_m ω A J)
    (.conj (sh_product_m T C ω) (.conj (sh_product_m D T J)
      (.conj (fn0_m D A K) (sh_select_m ω A R u C J T D K))))))
derive_free_closed sh_skolem_m

def Sh_hull_d (hKP : M.Models KP) (Z ω A T K U N : M.Domain) : Prop :=
  M.MemberSubset U N ∧ M.MemberSubset N A ∧ Fc_closed_d (kp_pair_l hKP) ω T K N ∧
    ∀ B, M.mem B Z → M.MemberSubset U B → M.MemberSubset B A →
      Fc_closed_d (kp_pair_l hKP) ω T K B → M.MemberSubset N B

def sh_hull_m {d} (ω A J T D K U N : Term d) : Formula 1 d :=
  .conj (Formula.subset U N) (.conj (Formula.subset N A) (.conj (sh_closed_m ω A J T D K N)
    (.forallE (.imp (Formula.subset U.weaken .newest) (.imp (Formula.subset .newest A.weaken)
      (.imp (sh_closed_m ω.weaken A.weaken J.weaken T.weaken D.weaken K.weaken .newest)
        (Formula.subset N.weaken .newest)))))))
derive_free_closed sh_hull_m

def sh_input_m {d} (ω A R U κ f : Term d) : Formula 1 d :=
  .conj (KP.ord0_m κ) (.conj (Formula.subset ω κ) (.conj (Formula.subset U A)
    (.conj (sh_bijection_m f κ U) (Formula.forallMem R
      (Formula.existsMem A.weaken (Formula.existsMem A.weaken.weaken (kpair0_m (.bound 2) (.bound 1) .newest)))))))
derive_free_closed sh_input_m

theorem sh_input_delta_l {d} (ω A R U κ f : Term d) : (sh_input_m ω A R U κ f).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (.atom _ _ _) (.conj (.atom _ _ _)
    (.conj (sh_bijection_delta_l ..) (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))))))

theorem sh_input_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A R U κ f : Term d) :
    Formula.satisfies ρ (sh_input_m ω A R U κ f) ↔
      M.IsOrdinal (κ.eval ρ) ∧ M.MemberSubset (ω.eval ρ) (κ.eval ρ) ∧ M.MemberSubset (U.eval ρ) (A.eval ρ) ∧
        M.IsSetBijectionFromTo (kp_pair_l hKP) (f.eval ρ) (κ.eval ρ) (U.eval ρ) ∧
          M.IsSetRelationOn (kp_pair_l hKP) (R.eval ρ) (A.eval ρ) := by
  simp only [sh_input_m, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP,
    Formula.satisfies_subset_iff, sh_bijection_sat_l hKP, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken]
  apply and_congr_right; intro _; apply and_congr_right; intro _
  apply and_congr_right; intro _; apply and_congr_right; intro _
  refine ⟨fun h => ⟨fun p hp => (h p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, b, hb.2⟩, ?_⟩, ?_⟩
  · rintro a b ⟨p, hp, hpr⟩
    obtain ⟨x, hx, y, hy, code⟩ := h p hpr
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code hp
    exact ⟨hx, hy⟩
  · intro h p hp
    obtain ⟨a, b, code⟩ := h.1 p hp
    exact ⟨a, (h.2 a b ⟨p, code, hp⟩).1, b, (h.2 a b ⟨p, code, hp⟩).2, code⟩

def Sh_data_d (hKP : M.Models KP) (Z ω c A U κ : M.Domain) : Prop :=
  ∃ u C J T D K N f, M.mem u Z ∧ M.mem C Z ∧ M.mem J Z ∧ M.mem T Z ∧ M.mem D Z ∧ M.mem K Z ∧
    M.mem N Z ∧ M.mem f Z ∧ Ssk_d (kp_pair_l hKP) ω c A u C J T D K ∧
      Sh_hull_d hKP Z ω A T K U N ∧ M.IsSetBijectionFromTo (kp_pair_l hKP) f κ N

def Sh_source_d (hKP : M.Models KP) (ω Z : M.Domain) : Prop := ∀ c A R U κ f,
  M.mem A Z → M.mem R Z → M.mem U Z → M.mem κ Z → M.mem f Z → Smdl_d (kp_pair_l hKP) c A R →
    M.IsOrdinal κ → M.MemberSubset ω κ → M.MemberSubset U A →
      M.IsSetBijectionFromTo (kp_pair_l hKP) f κ U → Sh_data_d hKP Z ω c A U κ

def sh_output_m {d} (ω A R U κ : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (sh_skolem_m (w ω) (w A) (w R) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
      (.conj (sh_hull_m (w ω) (w A) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (w U) (.bound 1))
        (sh_bijection_m .newest (w κ) (.bound 1)))))))))))
derive_free_closed sh_output_m

def sh_source_m {d} (ω : Term d) : Formula 1 d := .forallE (.forallE (.forallE (.forallE (.forallE
  (.imp (sh_input_m ω.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (sh_output_m ω.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1)))))))
derive_free_closed sh_source_m

end YesMetaZFC.SetTheory.Internal
