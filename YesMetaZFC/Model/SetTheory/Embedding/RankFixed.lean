import YesMetaZFC.Model.SetTheory.Source.FinitePartial
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis
import YesMetaZFC.SetTheory.Collapse.EmbeddingFixed
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion
import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra

/-! # 初等映射固定内部自然数并搬运有限函数

归纳使用实际图条目原公式，因而覆盖全部内部自然数。有限坐标保持据此
适用于非标准长度，不以宿主的有限列表代替对象模型中的序列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.natural_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) : ∀ n, M.mem n ω → M.PairMember I n n q := by
  let φ : UnarySchema 1 := { body := rd_entry_m .newest .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  have read n : φ.denote ρ n ↔ M.PairMember I n n q := rd_entry_sat_l hZF.1 ..
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z hz
      obtain ⟨z₀, hz₀, hzω⟩ := hω.1.1
      have eq := hZF.1.eq_of_same_members z₀ z (fun x => iff_of_false (hz₀ x) (hz x))
      subst z₀
      obtain ⟨z', _, hzz⟩ := hq.1.1.2.2 z (hX ω hωX z hzω)
      have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 1)
        (Formula.forallMem .newest .falsum) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])
        (.forallMem _ .falsum) ⟨fun _ => z, fun _ => z⟩ ⟨fun _ => z', fun _ => z'⟩ (fun _ => hzz)
      simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff] at tr
      have ez := hZF.1.eq_of_same_members z' z (fun x => iff_of_false (tr.mp hz x) (hz x))
      exact (read z).mpr (ez ▸ hzz)
    · intro n hnω ih m hs
      obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hnω
      have eq := Structure.SuccessorOf.eq hZF.1 hm₀ hs
      subst m₀
      obtain ⟨m', _, hmm⟩ := hq.1.1.2.2 m (hX ω hωX m hmω)
      have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 2)
        (KP.succ0_m .newest (.bound 1)) (by simp -implicitDefEqProofs)
        (KP.succ0_delta_l ..) ⟨Fin.cases m (fun _ => n), fun _ => n⟩
        ⟨Fin.cases m' (fun _ => n), fun _ => n⟩ (Fin.cases hmm (fun _ => (read n).mp ih))
      simp only [KP.succ0_sat_l hZF.1] at tr
      exact (read m).mpr (Structure.SuccessorOf.eq hZF.1 (tr.mp hs) hs ▸ hmm)
  exact fun n hn => (read n).mp (all n hn)

theorem Smap_d.function_l {ω c d X R Y S q A A' B B' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hA : M.PairMember I A A' q) (hB : M.PairMember I B B' q) (hf : M.PairMember I f f' q) :
    Fn0_d A B f ↔ Fn0_d A' B' f' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 3) (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..)
    ⟨Fin.cases f (Fin.cases B (fun _ => A)), fun _ => A⟩
    ⟨Fin.cases f' (Fin.cases B' (fun _ => A')), fun _ => A'⟩ (Fin.cases hf (Fin.cases hB (fun _ => hA)))
  simp only [fn0_sat_l hZF.1] at tr
  exact tr

theorem Smap_d.entry_l {ω c d X R Y S q a a' b b' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (ha : M.PairMember I a a' q) (hb : M.PairMember I b b' q) (hf : M.PairMember I f f' q) :
    Rd_entry_d a b f ↔ Rd_entry_d a' b' f' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 3) (rd_entry0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    ⟨Fin.cases f (Fin.cases b (fun _ => a)), fun _ => a⟩
    ⟨Fin.cases f' (Fin.cases b' (fun _ => a')), fun _ => a'⟩ (Fin.cases hf (Fin.cases hb (fun _ => ha)))
  simp only [rd_entry0_sat_l hZF.1] at tr
  exact tr

theorem Smap_d.forall_delta_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    {n} (φ : Formula 1 (n + 1)) (hc : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) q) :
    (∀ x, M.mem x X → Formula.satisfies (ρ.push x) φ) ↔ ∀ y, M.mem y Y → Formula.satisfies (η.push y) φ := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact spred_forall_delta_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hq⟩ hX hY φ hc hd ρ η hp

theorem Smap_d.subset_l {ω c d X R Y S q A A' B B' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hA : M.PairMember I A A' q) (hB : M.PairMember I B B' q) :
    M.MemberSubset A B ↔ M.MemberSubset A' B' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 2) (Formula.subset (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (.atom _ _ _) ⟨Fin.cases B (fun _ => A), fun _ => A⟩
    ⟨Fin.cases B' (fun _ => A'), fun _ => A'⟩ (Fin.cases hB (fun _ => hA))
  simp only [Formula.satisfies_subset_iff] at tr
  exact tr

theorem Smap_d.composition_l {ω c d X R Y S q A A' B B' C C' t t' f f' g g' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hA : Rd_entry_d A A' q) (hB : Rd_entry_d B B' q) (hC : Rd_entry_d C C' q)
    (ht : Rd_entry_d t t' q) (hf : Rd_entry_d f f' q) (hg : Rd_entry_d g g' q) :
    Cp0_d A B C t f g ↔ Cp0_d A' B' C' t' f' g' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hq (n := 6)
    (cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (cp0_delta_l ..)
    ⟨Fin.cases g (Fin.cases f (Fin.cases t (Fin.cases C (Fin.cases B (fun _ => A))))), fun _ => A⟩
    ⟨Fin.cases g' (Fin.cases f' (Fin.cases t' (Fin.cases C' (Fin.cases B' (fun _ => A'))))), fun _ => A'⟩
    (Fin.cases hg (Fin.cases hf (Fin.cases ht (Fin.cases hC (Fin.cases hB (fun _ => hA))))))
  simp only [cp0_sat_l hZF.1] at tr
  exact tr

theorem Smap_d.finite_fixed_l {ω c d X R Y S q n f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (hnω : M.mem n ω) (hfX : M.mem f X) (hf : Fn0_d n ω f) : M.PairMember I f f q := by
  obtain ⟨f', _, hff⟩ := hq.1.1.2.2 f hfX
  have natural := hq.natural_l hZF hω hX hY hm hn hωX
  have hf' := (hq.function_l hZF hω hX hY hm hn (natural n hnω) (hq.omega_l I hZF hω hX hY hm hn hωX) hff).mp hf
  have eq := hf'.ext_l hZF.1 hf (fun i hi => by
    obtain ⟨x, hx, hix⟩ := hf.2.1 i hi
    exact ⟨x, (hq.entry_l hZF hω hX hY hm hn (natural i (hω.transitive (ZF.modelsKP hZF) n hnω i hi)) (natural x hx) hff).mp hix, hix⟩)
  exact eq ▸ hff

theorem Smap_d.finite_injection_l {ω c d X R Y S q n A A' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (hnω : M.mem n ω) (hA : M.PairMember I A A' q) (hff : M.PairMember I f f' q)
    (hf : M.IsSetInjectionFromTo I f n A) : M.IsSetInjectionFromTo I f' n A' := by
  have natural := hq.natural_l hZF hω hX hY hm hn hωX
  have hf' := fn0_function_l (ZF.modelsKP hZF) ((hq.function_l hZF hω hX hY hm hn (natural n hnω) hA hff).mp
    (fn0_of_function_l (ZF.modelsKP hZF) hf.1))
  have back i y (hiy : Rd_entry_d i y f') : ∃ x, Rd_entry_d i x f ∧ M.PairMember I x y q := by
    have hi := hf'.input_mem_of_pairMember hiy
    obtain ⟨x, hx, hix⟩ := hf.1.2.2 i hi
    obtain ⟨x', _, hxx⟩ := hq.1.1.2.2 x (hX A (hq.1.1.input_mem_of_pairMember hA) x hx)
    have hix' := (hq.entry_l hZF hω hX hY hm hn (natural i (hω.transitive (ZF.modelsKP hZF) n hnω i hi)) hxx hff).mp hix
    exact ⟨x, hix, hf'.1.2 i x' y hix' hiy ▸ hxx⟩
  refine ⟨hf', fun i j y hi hj => ?_⟩
  obtain ⟨x, hix, hxy⟩ := back i y hi
  obtain ⟨z, hjz, hzy⟩ := back j y hj
  exact hf.2 i j z (hq.1.2 x z y hxy hzy ▸ hix) hjz

end YesMetaZFC.SetTheory.Internal

/-! ## 初等映射在序数上不下降

序数性的保持用 Δ₀ 刻画；不下降性对原图公式作内部成员归纳，
不要求背景模型外部良基，也不以外部递归替代模型中的证明。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.ordinal_l {ω c d X R Y S j a b : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hab : Rd_entry_d a b j) (ha : M.IsOrdinal a) : M.IsOrdinal b := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 1) (KP.ord0_m (.bound 0))
    (by simp -implicitDefEqProofs) (KP.ord0_delta_l ..)
    ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => hab)
  exact (KP.ord0_sat_l (ZF.modelsKP hZF) ..).mp (tr.mp ((KP.ord0_sat_l (ZF.modelsKP hZF) ..).mpr ha))

/-- 极限性在两侧传递模型中绝对，故随同一实际初等图保持。 -/
theorem Smap_d.limit_l {ω c d X R Y S j a b : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hab : Rd_entry_d a b j) : M.IsLimitOrdinal a ↔ M.IsLimitOrdinal b := by
  have hx := hj.1.1.input_mem_of_pairMember hab
  have hy := hj.1.1.output_mem_of_pairMember hab
  let nx : Nonempty {x // M.mem x X} := ⟨⟨a, hx⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨b, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨a, hx⟩, fun _ => ⟨a, hx⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨b, hy⟩, fun _ => ⟨b, hy⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l _ hz, hn.empty_pred_l _ hz, hj⟩
    nx ny (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs) ρ η (fun _ => hab)
  simp only [Formula.satisfies_isLimitOrdinal_iff] at tr
  exact (rt_limit_l hX nx (ZF.modelsKP hZF) ⟨a, hx⟩).symm.trans
    (tr.trans (rt_limit_l hY ny (ZF.modelsKP hZF) ⟨b, hy⟩))

theorem Smap_d.ordinal_le_l {ω c d X R Y S j a b : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hab : Rd_entry_d a b j) (ha : M.IsOrdinal a) : M.MemberSubset a b := by
  let ρ : Env M 1 := ⟨fun _ => j, fun _ => j⟩
  let φ : UnarySchema 1 := { body := .imp (KP.ord0_m .newest) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 2)) (Formula.subset (.bound 1) .newest))) }
  have sat α : φ.denote ρ α ↔ M.IsOrdinal α → ∀ β, Rd_entry_d α β j → M.MemberSubset α β := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, KP.ord0_sat_l (ZF.modelsKP hZF),
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff]; rfl
  apply (sat a).mp (ZF.mem_ind_l M hZF I φ ρ ?_ a) ha b hab
  intro α ih
  apply (sat α).mpr
  intro hα β hαβ γ hγα
  have hαX := hj.1.1.input_mem_of_pairMember hαβ
  have hγX := hX α hαX γ hγα
  obtain ⟨δ, _, hγδ⟩ := hj.1.1.2.2 γ hγX
  have hδβ := ((hn.2 δ β).mp ((hj.relation_l I hZF hω hm.1 hn.1 hγδ hαβ).mp
    ((hm.2 γ α).mpr ⟨hγX, hαX, hγα⟩))).2.2
  exact ordinal_down_l (ZF.modelsKP hZF) (hα.mem hγα) (hj.ordinal_l hZF hω hX hY hm hn hαβ hα)
    ((sat γ).mp (ih γ hγα) (hα.mem hγα) δ hγδ) hδβ

/-- 返回目标传递时，原序数本身也属于目标；无需把目标视为背景秩层。 -/
theorem Smap_d.ordinal_mem_l {ω c d X R Y S j a : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (ha : M.mem a X) (oa : M.IsOrdinal a) : M.mem a Y := by
  obtain ⟨b,hb,ab⟩ := hj.1.1.2.2 a ha
  have ob := hj.ordinal_l hZF hω hX hY hm hn ab oa
  have sub := hj.ordinal_le_l hZF hω hX hY hm hn ab oa
  rcases oa.trichotomy hZF.1 ob (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) a b) with eq | lt | gt
  · exact (hZF.1.eq_of_same_members a b eq).symm ▸ hb
  · exact hY b hb a lt
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) b (sub b gt)).elim

end YesMetaZFC.SetTheory.Internal

/-! ## 初等像中可数集合的逐元素回收

先反射源内的实际单射图，再用固定的自然数逐点回收其原像。
这给出可数集合的完整像方程，而非只有通常的单向包含。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.exists_delta_l {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    {n} (φ : Formula 1 (n+1)) (hc : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) j) :
    (∃ x, M.mem x X ∧ Formula.satisfies (ρ.push x) φ) ↔
      ∃ y, M.mem y Y ∧ Formula.satisfies (η.push y) φ := by
  have tr := hj.forall_delta_l hZF hω hX hY hm hn (.neg φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hc) (.neg hd) ρ η hp
  constructor
  · rintro ⟨x, hx, hs⟩
    apply Classical.byContradiction
    intro no
    exact (Formula.satisfies_neg_iff _ _).mp
      (tr.mpr (fun y hy => (Formula.satisfies_neg_iff _ _).mpr (fun h => no ⟨y, hy, h⟩)) x hx) hs
  · rintro ⟨y, hy, hs⟩
    apply Classical.byContradiction
    intro no
    exact (Formula.satisfies_neg_iff _ _).mp
      (tr.mp (fun x hx => (Formula.satisfies_neg_iff _ _).mpr (fun h => no ⟨x, hx, h⟩)) y hy) hs

/-- 可数性见证属于目标时，其原像中有实际见证，且每个目标成员都有原像。 -/
theorem Smap_d.countable_preimage_l {ω c d X R Y S j A B ι : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hωX : M.mem ω X) (hAB : Rd_entry_d A B j) (hι : M.mem ι Y)
    (inj : M.IsSetInjectionFromTo I ι B ω) :
    ∃ f, M.mem f X ∧ M.IsSetInjectionFromTo I f A ω ∧
      ∀ b, M.mem b B → ∃ a, M.mem a A ∧ Rd_entry_d a b j := by
  have fix := hj.omega_l I hZF hω hX hY hm hn hωX
  -- 先反射一个实际单射；随后借固定的自然数逐点反射其原像。
  let φ : Formula 1 3 := .conj (fn0_m (.bound 1) (.bound 2) .newest) (sc_index_m (.bound 2) (.bound 1) .newest)
  let ρ (D : M.Domain) : Env M 2 := ⟨Fin.cases D (fun _ => ω), fun _ => D⟩
  have read D f : Formula.satisfies ((ρ D).push f) φ ↔ Fn0_d D ω f ∧ Sc_index_d ω D f := by
    simp only [φ, Formula.satisfies_conj_iff, fn0_sat_l hZF.1, sc_index_sat_l (ZF.modelsKP hZF)]; rfl
  obtain ⟨f, hf, spec⟩ := (hj.exists_delta_l hZF hω hX hY hm hn φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.conj (fn0_delta_l ..) (sc_index_delta_l ..)) (ρ A) (ρ B) (Fin.cases hAB (fun _ => fix))).mpr
      ⟨ι, hι, (read B ι).mpr ⟨fn0_of_function_l (ZF.modelsKP hZF) inj.1,
        Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF)) inj⟩⟩
  obtain ⟨fn, idx⟩ := (read A f).mp spec
  obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f hf
  have gn := (hj.function_l hZF hω hX hY hm hn hAB fix hfg).mp fn
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (sc_index_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (sc_index_delta_l ..)
    ⟨Fin.cases f (Fin.cases A (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases g (Fin.cases B (fun _ => ω)), fun _ => ω⟩ (Fin.cases hfg (Fin.cases hAB (fun _ => fix)))
  have gidx : Sc_index_d ω B g := (sc_index_sat_l (ZF.modelsKP hZF) ..).mp
    (tr.mp ((sc_index_sat_l (ZF.modelsKP hZF) ..).mpr idx))
  refine ⟨f, hf, ⟨fn0_function_l (ZF.modelsKP hZF) fn, fun a b n ha hb =>
    idx.injective a (fn.bound_l ha).1 b (fn.bound_l hb).1 n (fn.bound_l ha).2 ha hb⟩, fun b hb => ?_⟩
  obtain ⟨n, hnω, hbn⟩ := gn.2.1 b hb
  have hnfix := hj.natural_l hZF hω hX hY hm hn hωX n hnω
  have pull := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (Formula.existsMem (.bound 2) (rd_entry0_m .newest (.bound 2) (.bound 1)))
    (by simp -implicitDefEqProofs) (.existsMem _ (rd_entry0_delta_l ..))
    ⟨Fin.cases f (Fin.cases n (fun _ => A)), fun _ => A⟩
    ⟨Fin.cases g (Fin.cases n (fun _ => B)), fun _ => B⟩ (Fin.cases hfg (Fin.cases hnfix (fun _ => hAB)))
  simp only [Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] at pull
  obtain ⟨a, ha, han⟩ := pull.mpr ⟨b, hb, hbn⟩
  obtain ⟨b', _, hab⟩ := hj.1.1.2.2 a (hX A (hj.1.1.input_mem_of_pairMember hAB) a ha)
  have hbn' := (hj.entry_l hZF hω hX hY hm hn hab hnfix hfg).mp han
  exact ⟨a, ha, gidx.injective b' (gn.bound_l hbn').1 b hb n hnω hbn' hbn ▸ hab⟩

/-- 有序对属于初等像时，两个坐标也有实际原像。 -/
theorem Smap_d.kpair_preimage_l {ω c d X R Y S j p q x y : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hp : Rd_entry_d p q j) (pair : KPair_d M q x y) :
    ∃ a b, M.mem a X ∧ M.mem b X ∧ KPair_d M p a b ∧ Rd_entry_d a x j ∧ Rd_entry_d b y j := by
  let φ : Formula 1 2 := Formula.existsMem (.bound 1)
    (Formula.existsMem .newest (kpair0_m (.bound 3) (.bound 2) .newest))
  have read p a : Formula.satisfies ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push a) φ ↔
      ∃ t, M.mem t p ∧ ∃ b, M.mem b t ∧ KPair_d M p a b := by
    simp only [φ, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  have hxY := (pair.mem_l M hY (hj.1.1.output_mem_of_pairMember hp)).1
  obtain ⟨t, ht, hyt⟩ := (kpair_union_l M pair y).mpr (Or.inr rfl)
  obtain ⟨a, ha, spec⟩ := (hj.exists_delta_l hZF hω hX hY hm hn φ (by simp -implicitDefEqProofs [φ])
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) ⟨fun _ => p, fun _ => p⟩ ⟨fun _ => q, fun _ => q⟩
    (fun _ => hp)).mpr ⟨x, hxY,
      (read q x).mpr ⟨t, ht, y, hyt, pair⟩⟩
  obtain ⟨_, _, b, _, code⟩ := (read p a).mp spec
  have hbX := (code.mem_l M hX (hj.1.1.input_mem_of_pairMember hp)).2
  obtain ⟨x', _, hx⟩ := hj.1.1.2.2 a ha
  obtain ⟨y', _, hy⟩ := hj.1.1.2.2 b hbX
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (kpair0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (kpair0_delta_l ..)
    ⟨Fin.cases b (Fin.cases a (fun _ => p)), fun _ => p⟩
    ⟨Fin.cases y' (Fin.cases x' (fun _ => q)), fun _ => q⟩ (Fin.cases hy (Fin.cases hx (fun _ => hp)))
  have image := (kpair0_sat_l hZF.1 ..).mp (tr.mp ((kpair0_sat_l hZF.1 ..).mpr code))
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M image pair
  exact ⟨a, b, ha, hbX, code, hx, hy⟩

/-- 源内可数的传递集合被逐点固定，目标中也有它到 ω 的实际单射。 -/
theorem Smap_d.countable_fixed_l {ω c d X R Y S j A ι : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hωX : M.mem ω X) (hA : M.mem A X) (hAt : M.TransitiveSet A) (hι : M.mem ι X)
    (inj : M.IsSetInjectionFromTo I ι A ω) :
    Rd_entry_d A A j ∧ (∀ x, M.mem x A → Rd_entry_d x x j) ∧
      ∃ η, M.mem η Y ∧ M.IsSetInjectionFromTo I η A ω := by
  obtain ⟨B, _, hAB⟩ := hj.1.1.2.2 A hA
  obtain ⟨η, hη, hi⟩ := hj.1.1.2.2 ι hι
  have fix := hj.omega_l I hZF hω hX hY hm hn hωX
  let φ : Formula 1 3 := .conj (Formula.forallMem (.bound 1) (Formula.subset .newest (.bound 2)))
    (.conj (fn0_m (.bound 1) (.bound 2) .newest) (sc_index_m (.bound 2) (.bound 1) .newest))
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.conj (.forallMem _ (.atom ..)) (.conj (fn0_delta_l ..) (sc_index_delta_l ..)))
    ⟨Fin.cases ι (Fin.cases A (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases η (Fin.cases B (fun _ => ω)), fun _ => ω⟩ (Fin.cases hi (Fin.cases hAB (fun _ => fix)))
  simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_subset_iff, fn0_sat_l hZF.1, sc_index_sat_l (ZF.modelsKP hZF)] at tr
  obtain ⟨hBt, fn, idx⟩ := tr.mp ⟨hAt, fn0_of_function_l (ZF.modelsKP hZF) inj.1,
    Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF)) inj⟩
  have count : M.IsSetInjectionFromTo I η B ω := ⟨fn0_function_l (ZF.modelsKP hZF) fn,
    fun a b n ha hb => idx.injective a (fn.bound_l ha).1 b (fn.bound_l hb).1 n (fn.bound_l ha).2 ha hb⟩
  obtain ⟨_, _, _, cover⟩ := hj.countable_preimage_l hZF hω hX hY hm hn hωX hAB hη count
  have rel x y u v (hx : Rd_entry_d x u j) (hy : Rd_entry_d y v j) : M.mem x y ↔ M.mem u v :=
    hj.member_l I hZF hω hm hn hx hy
  -- 可数性覆盖整个像；传递性及 Mostowski 唯一性固定其中每个元素。
  obtain ⟨_, point⟩ := mem_embedding_fixed_l hZF hX hj.1 rel hBt
    (fun x hx => (cover x hx).imp fun _ h => h.2)
  have eq : A = B := hZF.1.eq_of_same_members A B (fun x => ⟨fun hx => by
    obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x (hX A hA x hx)
    have hy := (rel x A y B hxy hAB).mp hx
    exact (hj.1.2 x y y hxy (point y hy)).symm ▸ hy,
    fun hx => (rel x A x B (point x hx) hAB).mpr hx⟩)
  subst B
  exact ⟨hAB, point, η, hη, count⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 逐点固定载体上的集合与图

有界成员公式固定子集；有序对公式固定坐标对；实际函数的全定义域和
逐点值确定整张函数图。关系图只需坐标落在固定载体内。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
theorem Smap_d.fixed_subset_l {ω c d X R Y S j A B : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hA : Rd_entry_d A A j)
    (point : ∀ x, M.mem x A → Rd_entry_d x x j) (hB : M.mem B X)
    (sub : M.MemberSubset B A) : Rd_entry_d B B j := by
  obtain ⟨C, _, hBC⟩ := hj.1.1.2.2 B hB
  have inside := (hj.subset_l hZF hω hX hY hm hn hBC hA).mp sub
  have mem x (hx : M.mem x A) : M.mem x B ↔ M.mem x C := by
    have rel := hj.relation_l I hZF hω hm.1 hn.1 (point x hx) hBC
    exact ⟨fun h => ((hn.2 x C).mp (rel.mp ((hm.2 x B).mpr
      ⟨hj.1.1.input_mem_of_pairMember (point x hx), hB, h⟩))).2.2,
      fun h => ((hm.2 x B).mp (rel.mpr ((hn.2 x C).mpr
        ⟨hj.1.1.output_mem_of_pairMember (point x hx), hj.1.1.output_mem_of_pairMember hBC, h⟩))).2.2⟩
  have eq := hZF.1.eq_of_same_members C B fun x =>
    ⟨fun hx => (mem x (inside x hx)).mpr hx, fun hx => (mem x (sub x hx)).mp hx⟩
  exact eq ▸ hBC

theorem Smap_d.kpair_l {ω c d X R Y S j p a b q a' b' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hpq : Rd_entry_d p q j) (ha : Rd_entry_d a a' j) (hb : Rd_entry_d b b' j) :
    KPair_d M p a b ↔ KPair_d M q a' b' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (kpair0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (kpair0_delta_l ..)
    ⟨Fin.cases b (Fin.cases a (fun _ => p)), fun _ => p⟩
    ⟨Fin.cases b' (Fin.cases a' (fun _ => q)), fun _ => q⟩ (Fin.cases hb (Fin.cases ha (fun _ => hpq)))
  simpa only [kpair0_sat_l hZF.1] using! tr

theorem Smap_d.fixed_pair_l {ω c d X R Y S j p a b : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hp : M.mem p X) (pair : KPair_d M p a b)
    (ha : Rd_entry_d a a j) (hb : Rd_entry_d b b j) : Rd_entry_d p p j := by
  obtain ⟨q, _, hpq⟩ := hj.1.1.2.2 p hp
  exact kpair_unique_l M hZF.1 ((hj.kpair_l hZF hω hX hY hm hn hpq ha hb).mp pair) pair ▸ hpq

theorem Smap_d.fixed_relation_l {ω c d X R Y S j A f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hA : Rd_entry_d A A j)
    (point : ∀ x, M.mem x A → Rd_entry_d x x j) (hf : M.mem f X)
    (rel : M.IsSetRelationOn I f A) : Rd_entry_d f f j := by
  obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f hf
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  let ρ (g : M.Domain) : Env M 2 := ⟨Fin.cases g (fun _ => A), fun _ => A⟩
  have read g : Formula.satisfies (ρ g) φ ↔ ∀ p, M.mem p g →
      ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ KPair_d M p a b := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))) (ρ f) (ρ g) (Fin.cases hfg (fun _ => hA))
  have bound := (read g).mp (tr.mp ((read f).mpr (fun p hp => by
    obtain ⟨a, b, pair⟩ := rel.1 p hp
    have ab := rel.2 a b ⟨p, pair, hp⟩
    exact ⟨a, ab.1, b, ab.2, pair⟩)))
  have entry a b (ha : M.mem a A) (hb : M.mem b A) :=
    hj.entry_l hZF hω hX hY hm hn (point a ha) (point b hb) hfg
  have eq := hZF.1.eq_of_same_members g f fun p => ⟨fun hp => by
    obtain ⟨a, ha, b, hb, pair⟩ := bound p hp
    obtain ⟨q, pq, hq⟩ := (entry a b ha hb).mpr ⟨p, pair, hp⟩
    exact kpair_unique_l M hZF.1 pq pair ▸ hq, fun hp => by
      obtain ⟨a, b, pair⟩ := rel.1 p hp
      have ab := rel.2 a b ⟨p, pair, hp⟩
      obtain ⟨q, pq, hq⟩ := (entry a b ab.1 ab.2).mp ⟨p, pair, hp⟩
      exact kpair_unique_l M hZF.1 pq pair ▸ hq⟩
  exact eq ▸ hfg

/-- 固定载体上的关系若属于初等像，其原像仍是同一张关系图。 -/
theorem Smap_d.relation_preimage_l {ω c d X R Y S j A f g : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hA : Rd_entry_d A A j) (point : ∀ x, M.mem x A → Rd_entry_d x x j)
    (hfg : Rd_entry_d f g j) (rel : M.IsSetRelationOn I g A) : f = g := by
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases f (fun _ => A), fun _ => A⟩ ⟨Fin.cases g (fun _ => A), fun _ => A⟩ (Fin.cases hfg (fun _ => hA))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have shape := tr.mpr (fun p hp => by
    obtain ⟨a, b, pair⟩ := rel.1 p hp
    have ab := rel.2 a b ⟨p, pair, hp⟩
    exact ⟨a, ab.1, b, ab.2, pair⟩)
  have small : M.IsSetRelationOn I f A := ⟨fun p hp =>
    (shape p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, b, hb.2⟩, fun a b ⟨p, pair, hp⟩ => by
      obtain ⟨x, hx, y, hy, code⟩ := shape p hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M code pair
      exact ⟨hx, hy⟩⟩
  exact hj.1.1.1.2 f f g (hj.fixed_relation_l hZF hω hX hY hm hn hA point
    (hj.1.1.input_mem_of_pairMember hfg) small) hfg

/-- 值域无需整体固定；固定定义域和每个实际函数值已经足够。 -/
theorem Smap_d.fixed_function_l {ω c d X R Y S j D B f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hD : Rd_entry_d D D j) (point : ∀ x, M.mem x D → Rd_entry_d x x j)
    (hB : M.mem B X) (hf : M.mem f X) (fn : Fn0_d D B f)
    (values : ∀ x y, Rd_entry_d x y f → Rd_entry_d y y j) : Rd_entry_d f f j := by
  obtain ⟨C, _, hBC⟩ := hj.1.1.2.2 B hB
  obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f hf
  have second := (hj.function_l hZF hω hX hY hm hn hD hBC hfg).mp fn
  have eq := second.ext_l hZF.1 fn fun x hx => by
    obtain ⟨y, _, hxy⟩ := fn.2.1 x hx
    exact ⟨y, (hj.entry_l hZF hω hX hY hm hn (point x hx) (values x y hxy) hfg).mp hxy, hxy⟩
  exact eq ▸ hfg

end YesMetaZFC.SetTheory.Internal

/-! ## 固定字母表上的全部有限历史

先固定每张有限函数图，再用有限空间的有界上界证明固定整个空间。
这里不估计空间或收缩图的秩，也不要求目标模型包含额外的幂集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.fixed_fseq_l {ω c d X R Y S j A F : M.Domain}
    (hw : M.IsOmega ω) (tx : M.TransitiveSet X) (ty : M.TransitiveSet Y)
    (source : Smem_d I c X R) (target : Smem_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hω : M.mem ω X) (ha : Rd_entry_d A A j) (letters : ∀ x, M.mem x A → Rd_entry_d x x j)
    (hF : M.mem F X) (space : Fseq_space_d I ω A F) :
    Rd_entry_d F F j ∧ ∀ s, M.mem s F → Rd_entry_d s s j := by
  have naturals := map.natural_l hZF hw tx ty source target hω
  have finite s (hs : M.mem s F) : Rd_entry_d s s j := by
    obtain ⟨n,hn,fn⟩ := (space s).mp hs
    exact map.fixed_function_l hZF hw tx ty source target (naturals n hn)
      (fun i hi => naturals i (hw.transitive (ZF.modelsKP hZF) n hn i hi))
      (map.1.1.input_mem_of_pairMember ha) (tx F hF s hs) (fn0_of_function_l (ZF.modelsKP hZF) fn)
      (fun _ y entry => letters y (fn.output_mem_of_pairMember entry))
  obtain ⟨G,hG,fg⟩ := map.1.1.2.2 F hF
  let φ : Formula 1 3 := .forallMem (.bound 2)
    (.existsMem (.bound 1) (fn0_m .newest (.bound 3) (.bound 1)))
  let ρ (K : M.Domain) : Env M 3 := ⟨Fin.cases ω (Fin.cases A (fun _ => K)),fun _ => K⟩
  have sat K : Formula.satisfies (ρ K) φ ↔ ∀ s, M.mem s K →
      ∃ n, M.mem n ω ∧ Fn0_d n A s := by
    simp only [φ,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,fn0_sat_l hZF.1]
    rfl
  have moved := smap_delta_l I hZF hw tx ty source target map φ
    (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (fn0_delta_l ..))) (ρ F) (ρ G)
    (Fin.cases (map.omega_l I hZF hw tx ty source target hω) (Fin.cases ha (fun _ => fg)))
  have bound := (sat G).mp (moved.mp ((sat F).mpr (fun s hs => by
    obtain ⟨n,hn,fn⟩ := (space s).mp hs
    exact ⟨n,hn,fn0_of_function_l (ZF.modelsKP hZF) fn⟩)))
  have eq : G = F := hZF.1.eq_of_same_members G F (fun s => ⟨fun hs => by
    obtain ⟨n,hn,fn⟩ := bound s hs
    exact (space s).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fn⟩,fun hs => by
      have rel := map.relation_l I hZF hw source.1 target.1 (finite s hs) fg
      exact ((target.2 s G).mp (rel.mp ((source.2 s F).mpr ⟨tx F hF s hs,hF,hs⟩))).2.2⟩)
  exact ⟨eq ▸ fg,finite⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 共同相对秩段的逐点固定

先在共同载体中比较两份原历史，再将源历史的像与目标历史比较。
低序数固定给出每个低层整体固定；对层号作强归纳，子集保持给出逐点固定。
不要求载体满足 ZF，也不预设临界点在背景中不可达。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.rank_fixed_l {ω c d X R Y S j κ ℓ V : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hκ : Rd_entry_d κ ℓ j) (fixed : ∀ β, M.mem β κ → Rd_entry_d β β j)
    (hV : M.mem V X) (rx : Vr_d X κ V) (hV' : M.mem V Y) (ry : Vr_d Y κ V) :
    ∀ x, M.mem x V → Rd_entry_d x x j := by
  have vt := rx.transitive_l hX hV
  obtain ⟨B, F, hB, hF, cx⟩ := rx
  obtain ⟨C, G, hC, _, cy⟩ := ry
  have ff := (cx V hV).2.1
  have gf := (cy V hV').2.1
  have ho := (cx V hV).1
  have low δ U (hu : Rd_entry_d δ U F) : M.mem U V :=
    ((cx U (hX B hB U (ff.bound_l hu).2)).2.2.2).mpr
      ⟨δ, (ff.bound_l hu).1, U, (ff.bound_l hu).2, hu, fun _ h => h⟩
  have low' δ U (hu : Rd_entry_d δ U G) : M.mem U V :=
    ((cy U (hY C hC U (gf.bound_l hu).2)).2.2.2).mpr
      ⟨δ, (gf.bound_l hu).1, U, (gf.bound_l hu).2, hu, fun _ h => h⟩
  have same := vc_history_eq_l hZF vt ff gf ho (fun _ h => h)
    (fun δ hδ U hu => ⟨low δ U hu, fun t ht =>
      (cx t (hX V hV t ht)).2.2.1 δ hδ U (ff.bound_l hu).2 hu⟩)
    (fun δ hδ U hu => ⟨low' δ U hu, fun t ht =>
      (cy t (hY V hV' t ht)).2.2.1 δ hδ U (gf.bound_l hu).2 hu⟩)
  obtain ⟨V', hV'Y, iV⟩ := hj.1.1.2.2 V hV
  obtain ⟨B', hB', iB⟩ := hj.1.1.2.2 B hB
  obtain ⟨F', _, iF⟩ := hj.1.1.2.2 F hF
  let ψ : Formula 1 5 := vc_matrix_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := hj.forall_delta_l hZF hω hX hY mx my ψ (by simp -implicitDefEqProofs [ψ])
    (vc_matrix_delta_l ..) ⟨Fin.cases F (Fin.cases B (Fin.cases V (fun _ => κ))), fun _ => κ⟩
    ⟨Fin.cases F' (Fin.cases B' (Fin.cases V' (fun _ => ℓ))), fun _ => ℓ⟩
    (Fin.cases iF (Fin.cases iB (Fin.cases iV (fun _ => hκ))))
  simp only [ψ, vc_matrix_sat_l (ZF.modelsKP hZF)] at tr
  have ci := tr.mp cx
  have fi := (ci V' hV'Y).2.1
  have sub β (hβ : M.mem β κ) := (hj.member_l I hZF hω mx my (fixed β hβ) hκ).mp hβ
  have images := vc_history_eq_l hZF hY fi gf ho sub
    (fun δ hδ U hu => ⟨hY B' hB' U (fi.bound_l hu).2, fun t ht =>
      (ci t ht).2.2.1 δ (sub δ hδ) U (fi.bound_l hu).2 hu⟩)
    (fun δ hδ U hu => ⟨hY C hC U (gf.bound_l hu).2, fun t ht =>
      (cy t ht).2.2.1 δ hδ U (gf.bound_l hu).2 hu⟩)
  have level β (hβ : M.mem β κ) U (hu : Rd_entry_d β U F) : Rd_entry_d U U j := by
    obtain ⟨U', _, iU⟩ := hj.1.1.2.2 U (hX V hV U (low β U hu))
    obtain ⟨W, _, hw⟩ := gf.2.1 β hβ
    have hu' := (hj.entry_l hZF hω hX hY mx my (fixed β hβ) iU iF).mp hu
    exact ((images β hβ U' W hu' hw).trans (same β hβ U W hu hw).symm) ▸ iU
  let ρ : Env M 3 := ⟨Fin.cases κ (Fin.cases F (fun _ => j)), fun _ => κ⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 3))
      (Formula.forallMem .newest (rd_entry0_m .newest .newest (.bound 5))))) }
  have sat β : φ.denote ρ β ↔ M.mem β κ → ∀ U, Rd_entry_d β U F →
      ∀ x, M.mem x U → Rd_entry_d x x j := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1]; rfl
  have point β (hβ : M.mem β κ) : ∀ U, Rd_entry_d β U F → ∀ x, M.mem x U → Rd_entry_d x x j := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ U hu x hx
    have hxX := hX V hV x (vt U (low β U hu) x hx)
    obtain ⟨γ, hγ, W, _, hw, bound⟩ := ((cx x hxX).2.2.1 β hβ U (ff.bound_l hu).2 hu).mp hx
    exact hj.fixed_subset_l hZF hω hX hY mx my (level γ (ho.transitive β hβ γ hγ) W hw)
      ((sat γ).mp (ih γ hγ) (ho.transitive β hβ γ hγ) W hw) hxX bound
  intro x hx
  have hxX := hX V hV x hx
  obtain ⟨β, hβ, U, _, hu, bound⟩ := ((cx x hxX).2.2.2).mp hx
  exact hj.fixed_subset_l hZF hω hX hY mx my (level β hβ U hu) (point β hβ U hu) hxX bound

end YesMetaZFC.SetTheory.Internal
