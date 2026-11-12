import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.Model.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Collapse.RelationRank
import YesMetaZFC.SetTheory.Descriptive.Normal.Closed

/-! # 任意字母表前缀树的有界子边

长度、字母和函数图均限制在实际集合内；子边因而是 Δ₀，可在传递源中分离。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tb_step_d (ω A s t : M.Domain) : Prop := ∃ n, M.mem n ω ∧ ∃ m, M.mem m ω ∧
  Fn0_d n A s ∧ Fn0_d m A t ∧ M.SuccessorOf m n ∧ M.MemberSubset s t

def tb_step_m {n} (ω A s t : Term n) : Formula 1 n := Formula.existsMem ω
  (Formula.existsMem ω.weaken (.conj (fn0_m (.bound 1) A.weaken.weaken s.weaken.weaken)
    (.conj (fn0_m .newest A.weaken.weaken t.weaken.weaken)
      (.conj (KP.succ0_m .newest (.bound 1)) (Formula.subset s.weaken.weaken t.weaken.weaken)))))
derive_free_closed tb_step_m

theorem tb_step_delta_l {n} (ω A s t : Term n) : (tb_step_m ω A s t).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.atom _ _ _)))))

theorem tb_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A s t : Term n) :
    Formula.satisfies ρ (tb_step_m ω A s t) ↔ Tb_step_d (ω.eval ρ) (A.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [tb_step_m, Tb_step_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, KP.succ0_sat_l hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

theorem tb_step_l (hZF : M.Models ZF) {ω A J s t : M.Domain} (hω : M.IsOmega ω)
    (hJ : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A J) (hs : M.mem s J) (ht : M.mem t J) :
    Tb_step_d ω A s t ↔ Step_d (kp_pair_l (ZF.modelsKP hZF)) ω s t := by
  obtain ⟨n, hn, hsn⟩ := (hJ s).mp hs
  obtain ⟨m, hm, htm⟩ := (hJ t).mp ht
  refine ⟨fun ⟨l, hl, k, hk, hf, hg, h⟩ =>
    (tree_step_iff_l _ hZF hω hl hk (fn0_function_l (ZF.modelsKP hZF) hf) (fn0_function_l (ZF.modelsKP hZF) hg)).mpr h,
    fun h => ⟨n, hn, m, hm, fn0_of_function_l (ZF.modelsKP hZF) hsn, fn0_of_function_l (ZF.modelsKP hZF) htm,
      (tree_step_iff_l _ hZF hω hn hm hsn htm).mp h⟩⟩

/-- 实际无限枝的全部有限前缀组成真实 ω 下降链。 -/
theorem tree_branch_desc_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF) {ω A J T R f : M.Domain} (hω : M.IsOmega ω)
    (hJ : Fseq_space_d I ω A J)
    (hf : M.IsSetFunctionFromTo I f ω A)
    (hb : Branch_d J T f) (hr : Edge_d I ω T R) :
    ∃ G, Fn0_d ω T G ∧ Wf_desc_d R G := by
  let φ : BinarySchema 1 := { body := Formula.isRestriction 𝒞 .newest (.bound 2) (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
  have sat n s : φ.denote ρ n s ↔ M.IsRestrictionOf I s f n := Formula.satisfies_isRestriction_iff I ..
  obtain ⟨G, fn, select⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ (source := ω) (target := T)
    (fun n hn => (ds_prefix_l I hZF hω hf hn).imp fun s hs => (sat n s).mpr hs.2.1)
    (fun _ _ _ _ hs ht => ((sat ..).mp hs).eq hZF.1 ((sat ..).mp ht))
    (fun n s hn hs => by
      have res := (sat n s).mp hs
      have fn := res.isSetFunctionFromTo hf (hω.transitive (ZF.modelsKP hZF) n hn)
      exact hb s ((hJ s).mpr ⟨n, hn, fn⟩) ((ds_restrict_iff_l I fn hf.1).mp res))
  refine ⟨G, fn0_of_function_l (ZF.modelsKP hZF) fn, fun i j s t hs hi hj => ?_⟩
  have si := (sat i s).mp ((select i s).mp hi).2
  have tj := (sat j t).mp ((select j t).mp hj).2
  have hiω := fn.input_mem_of_pairMember hi
  have hjω := fn.input_mem_of_pairMember hj
  have sfn := si.isSetFunctionFromTo hf (hω.transitive (ZF.modelsKP hZF) i hiω)
  have tfn := tj.isSetFunctionFromTo hf (hω.transitive (ZF.modelsKP hZF) j hjω)
  exact (hr.2 s t).mpr ⟨fn.output_mem_of_pairMember hi, fn.output_mem_of_pairMember hj,
    (tree_step_iff_l I hZF hω hiω hjω sfn tfn).mpr
      ⟨hs, ds_prefix_mono_l I sfn tfn.1 si tj (fun n hn => (hs n).mpr (Or.inl hn))⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 任意集合字母表上的无枝树与良基性

依赖选择只用于无死节点树上的逐项延长链；链的并与良基秩均在 ZF 中构造。
内部长度遍历原模型的整个 ω，不要求字母表可数或 ω 外部标准。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable (hZF : M.Models ZF)
include hZF

theorem tree_pruned_dc_l {ω X F T : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (ne : ∃ s, M.mem s T)
    (next : ∀ s, M.mem s T → ∃ t, M.mem t T ∧ Step_d I ω s t) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ Branch_d F T f := by
  let φ : BinarySchema 1 := { body := step_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  obtain ⟨R, _, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ⟨fun _ => ω, fun _ => ω⟩ T
  have edges s t : M.PairMember I s t R ↔ M.mem s T ∧ M.mem t T ∧ Step_d I ω s t :=
    (read s t).trans (and_congr_right fun _ => and_congr_right fun _ => step_sat_l I hZF.1 ..)
  obtain ⟨e, he, heω⟩ := hω.1.1
  have root := ne.elim fun s hs => tree.2 s hs e ((space e).mpr ⟨e, heω, ds_empty_fun_l I he⟩)
    (fun x hx => (he x hx).elim)
  obtain ⟨H, fn, zero, chain⟩ := dc T R e root
    (fun s hs => (next s hs).imp fun t ht => ⟨ht.1, (edges s t).mpr ⟨hs, ht⟩⟩)
  obtain ⟨f, ff, path⟩ := ds_path_run_l I hZF hω (fun s hs => (space s).mp (tree.1 s hs)) fn he zero
    (fun i j s t hj hs ht => ((edges s t).mp (chain i j s t hj hs ht)).2.2)
  refine ⟨f,ff,(tree_branch_l I hZF hω space ff).mpr (fun n hn => ?_)⟩
  obtain ⟨s,hs,ns⟩ := fn.2.2 n hn
  exact ⟨s,hs,(ds_restrict_iff_l I (path n s ns).1 ff.1).mpr (path n s ns).2⟩

theorem tree_wf_dc_l {ω X F T R : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (edges : Edge_d I ω T R)
    (no : ∀ f, M.IsSetFunctionFromTo I f ω X → ¬ Branch_d F T f) : Wf_rel_d T R := by
  classical
  intro Q sub ne
  apply Classical.byContradiction
  intro bad
  have next q (hq : M.mem q Q) : ∃ v, M.mem v Q ∧ Step_d I ω q v := by
    apply Classical.byContradiction
    intro no
    exact bad ⟨q, hq, fun v hv edge => no ⟨v, hv, ((edges.2 q v).mp edge).2.2⟩⟩
  obtain ⟨P, read⟩ := ktree_exists_l (ZF.modelsKP hZF) F Q
  have contained s (hs : M.mem s P) : M.mem s T :=
    ((read s).mp hs).2.elim fun q hq => tree.2 q (sub q hq.1) s ((read s).mp hs).1 hq.2
  have pruned s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Step_d I ω s t := by
    obtain ⟨hsF, q, hq, sq⟩ := (read s).mp hs
    obtain ⟨v, hv, qv⟩ := next q hq
    obtain ⟨n, hn, fs⟩ := (space s).mp hsF
    obtain ⟨l, hl, fq⟩ := (space q).mp (tree.1 q (sub q hq))
    obtain ⟨m, hm, fv⟩ := (space v).mp (tree.1 v (sub v hv))
    obtain ⟨succ, qv⟩ := (tree_step_iff_l I hZF hω hl hm fq fv).mp qv
    have nl : M.MemberSubset n l := fun i hi => by
      obtain ⟨a, _, value⟩ := fs.2.2 i hi
      exact fq.input_mem_of_pairMember (value.elim fun p hp => ⟨p, hp.1, sq p hp.2⟩)
    have nm : M.mem n m := by
      rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn l hl with eq | lt | gt
      · exact (hZF.1.eq_of_same_members n l eq).symm ▸ succ.predecessor_mem
      · exact (succ n).mpr (Or.inl lt)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (nl l gt)).elim
    obtain ⟨u, su, hu⟩ := hω.1.2 n hn
    have um : M.MemberSubset u m := fun i hi => ((su i).mp hi).elim
      (fun hi => (succ i).mpr (Or.inl (nl i hi))) (fun eq => (hZF.1.eq_of_same_members i n eq).symm ▸ nm)
    obtain ⟨t, rt⟩ := ZF.exists_restriction hZF I v u
    have ft := rt.isSetFunctionFromTo fv um
    have st := ds_prefix_mono_l I fs ft.1 ((ds_restrict_iff_l I fs fv.1).mpr
      (fun p hp => qv p (sq p hp))) rt (fun i hi => (su i).mpr (Or.inl hi))
    exact ⟨t, (read t).mpr ⟨(space t).mpr ⟨u, hu, ft⟩, v, hv, (ds_restrict_iff_l I ft fv.1).mp rt⟩,
      (tree_step_iff_l I hZF hω hn hu fs ft).mpr ⟨su, st⟩⟩
  have treeP : Tree_d F P := ⟨fun s hs => ((read s).mp hs).1, fun s hs t ht ts => by
    obtain ⟨_, q, hq, sq⟩ := (read s).mp hs
    exact (read t).mpr ⟨ht, q, hq, fun x hx => sq x (ts x hx)⟩⟩
  have neP := ne.imp fun q hq => (read q).mpr ⟨tree.1 q (sub q hq), q, hq, fun _ hx => hx⟩
  obtain ⟨f, ff, branch⟩ := tree_pruned_dc_l I hZF hω dc space treeP neP pruned
  exact no f ff (fun s hs sf => contained s (branch s hs sf))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 有限前缀树上的秩沿任意真延长下降

对较长节点的内部长度归纳，把任意延长分解为一个末项和较短前缀。
中间前缀由实际树的向下封闭性给出，所有秩值来自同一函数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tb_rank_prefix_l {ω X F R α H : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F R) (ordinal : M.IsOrdinal α)
    (rank : Fn0_d R α H)
    (decrease : ∀ s t a b, Rd_entry_d s a H → Rd_entry_d t b H → Tb_step_d ω X s t → M.mem b a) :
    ∀ s t a b, Rd_entry_d s a H → Rd_entry_d t b H → M.MemberSubset s t → s ≠ t → M.mem b a := by
  let η : Env M 2 := ⟨Fin.cases X (fun _ => H), fun _ => X⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ t b,
    ⌜fn0_m⌝ₚ(⌜(Term.bound 0 : Term 3)⌝ₛ, ⌜(Term.bound 1 : Term 3)⌝ₛ, t) →
    ⌜rd_entry0_m⌝ₚ(t, b, ⌜(Term.bound 2 : Term 3)⌝ₛ) → ∀ s a,
    ⌜rd_entry0_m⌝ₚ(s, a, ⌜(Term.bound 2 : Term 3)⌝ₛ) → s ⊆ t → s = t ∨ b ∈ a⟫ }
  have sat n : φ.denote η n ↔ ∀ t b, Fn0_d n X t → Rd_entry_d t b H →
      ∀ s a, Rd_entry_d s a H → M.MemberSubset s t → s = t ∨ M.mem b a := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_mem_iff,
      Definitional.Term.eval_weaken]; rfl
  have all := hw.induction (fun n => ∀ t b, Fn0_d n X t → Rd_entry_d t b H →
      ∀ s a, Rd_entry_d s a H → M.MemberSubset s t → s = t ∨ M.mem b a) (by
    obtain ⟨D, ds⟩ := ZF.separation_exists_d hZF φ η ω
    exact ⟨D, fun n => (ds n).trans (and_congr_right fun _ => sat n)⟩) (by
    intro e he t b ft _ s a _ sub
    have ft := fn0_function_l (ZF.modelsKP hZF) ft
    have empty p (hp : M.mem p t) : False := by
      obtain ⟨i, x, pair⟩ := ft.1.1 p hp
      exact he i (ft.input_mem_of_pairMember ⟨p, pair, hp⟩)
    exact Or.inl (hZF.1.eq_of_same_members s t (fun p => iff_of_false (fun hp => empty p (sub p hp)) (empty p)))) (by
    intro n hn ih m succ t b ft ht s a hs sub
    classical
    by_cases eq : s = t
    · exact Or.inl eq
    have htR := (rank.bound_l ht).1
    have hsR := (rank.bound_l hs).1
    obtain ⟨k, hk, fs⟩ := (space s).mp (tree.1 s hsR)
    have ft' := fn0_function_l (ZF.modelsKP hZF) ft
    obtain ⟨m', sm', hm'⟩ := hw.1.2 n hn
    have hm : M.mem m ω := sm'.eq hZF.1 succ ▸ hm'
    have km : M.MemberSubset k m := fun i hi => by
      obtain ⟨x, _, p, pair, hp⟩ := fs.2.2 i hi
      exact ft'.input_mem_of_pairMember ⟨p, pair, sub p hp⟩
    have km' : M.mem k m := by
      rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare k hk m hm with e | lt | gt
      · have e := hZF.1.eq_of_same_members k m e
        have res := (ds_restrict_iff_l I fs ft'.1).mpr sub
        have own := (ds_restrict_iff_l I ft' ft'.1).mpr (fun _ h => h)
        exact (eq ((e ▸ res).eq hZF.1 own)).elim
      · exact lt
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) m (km m gt)).elim
    have kn : M.MemberSubset k n := ((succ k).mp km').elim
      (fun h => (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive k h)
      (fun e => (hZF.1.eq_of_same_members k n e).symm ▸ (fun _ h => h))
    obtain ⟨p, res⟩ := ZF.exists_restriction hZF I t n
    have fp := res.isSetFunctionFromTo ft' (fun i hi => (succ i).mpr (Or.inl hi))
    have pt := (ds_restrict_iff_l I fp ft'.1).mp res
    have hpR := tree.2 t htR p ((space p).mpr ⟨n, hn, fp⟩) pt
    obtain ⟨r, _, hr⟩ := rank.2.1 p hpR
    have sp := ds_prefix_mono_l I fs fp.1 ((ds_restrict_iff_l I fs ft'.1).mpr sub) res kn
    have br := decrease p t r b hr ht ⟨n, hn, m, hm, fn0_of_function_l (ZF.modelsKP hZF) fp, ft, succ, pt⟩
    exact Or.inr ((ih p r (fn0_of_function_l (ZF.modelsKP hZF) fp) hr s a hs sp).elim
      (fun e => ((fn0_function_l (ZF.modelsKP hZF) rank).1.2 s r a (e.symm ▸ hr) hs) ▸ br)
      (fun ra => (ordinal.mem (rank.bound_l hs).2).transitive r ra b br)))
  intro s t a b hs ht sub ne
  obtain ⟨n, hn, ft⟩ := (space t).mp (tree.1 t (rank.bound_l ht).1)
  exact (all n hn t b (fn0_of_function_l (ZF.modelsKP hZF) ft) ht s a hs sub).elim (fun eq => (ne eq).elim) id

end YesMetaZFC.SetTheory.Descriptive

/-! ## 任意集合树的序数秩证书

DC 只用于从无枝性推出良基性。产生实际有界秩之后，排除新分支只需 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Cg_rank_d (ω X R α F : M.Domain) : Prop where
  ordinal : M.IsOrdinal α
  function : Fn0_d R α F
  decrease : ∀ s t a b, Rd_entry_d s a F → Rd_entry_d t b F → Tb_step_d ω X s t → M.mem b a
  proper : ∀ s t a b, Rd_entry_d s a F → Rd_entry_d t b F → M.MemberSubset s t → s ≠ t → M.mem b a

def cg_rank0_m {d} (ω X R α F : Term d) : Formula 1 d := set[d] ⟪
  ⌜KP.ord0_m⌝ₚ(⌜α⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜R⌝ₛ, ⌜α⌝ₛ, ⌜F⌝ₛ) ∧
  (∀ s ∈ ⌜R⌝ₛ, ∀ t ∈ ⌜R⌝ₛ, ∀ a ∈ ⌜α⌝ₛ, ∀ b ∈ ⌜α⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(s, a, ⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(t, b, ⌜F⌝ₛ) →
    ⌜tb_step_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, s, t) → b ∈ a) ∧
  (∀ s ∈ ⌜R⌝ₛ, ∀ t ∈ ⌜R⌝ₛ, ∀ a ∈ ⌜α⌝ₛ, ∀ b ∈ ⌜α⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(s, a, ⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(t, b, ⌜F⌝ₛ) → s ⊆ t → ¬ (s = t) → b ∈ a)⟫
derive_free_closed cg_rank0_m

theorem cg_rank0_delta_l {d} (ω X R α F : Term d) : (cg_rank0_m ω X R α F).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (fn0_delta_l ..) (.conj
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (tb_step_delta_l ..) (.mem ..))))))))
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (.atom ..) (.imp (.neg (.atom ..)) (.mem ..)))))))))))

theorem cg_rank0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω X R α F : Term d) :
    Formula.satisfies ρ (cg_rank0_m ω X R α F) ↔
      Cg_rank_d (ω.eval ρ) (X.eval ρ) (R.eval ρ) (α.eval ρ) (F.eval ρ) := by
  simp only [cg_rank0_m, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP, fn0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    tb_step_sat_l hKP.1, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨ha, fn, decrease, proper⟩ => ⟨ha, fn, fun s t a b hs ht step => decrease s (fn.bound_l hs).1
      t (fn.bound_l ht).1 a (fn.bound_l hs).2 b (fn.bound_l ht).2 hs ht step,
      fun s t a b hs ht => proper s (fn.bound_l hs).1 t (fn.bound_l ht).1 a (fn.bound_l hs).2 b (fn.bound_l ht).2 hs ht⟩,
    fun rank => ⟨rank.ordinal, rank.function, fun s _ t _ a _ b _ => rank.decrease s t a b,
      fun s _ t _ a _ b _ => rank.proper s t a b⟩⟩

def cg_rank_m {d} (ω X R : Term d) : Formula 1 d := .existsE (.existsE
  (cg_rank0_m ω.weaken.weaken X.weaken.weaken R.weaken.weaken (.bound 1) .newest))
derive_free_closed cg_rank_m

include hZF in
/-- 实际秩函数排除任意内部无限逐项延长链；这里不再使用 DC。 -/
theorem Cg_rank_d.no_chain_l {ω X R α F H : M.Domain} (hω : M.IsOmega ω)
    (rank : Cg_rank_d ω X R α F) (fn : Fn0_d ω R H) :
    ¬ (∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H → Tb_step_d ω X s t) := by
  intro next
  obtain ⟨G, gf, read⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) fn) (fn0_function_l (ZF.modelsKP hZF) rank.function)
  obtain ⟨E, wf, edges⟩ := wf_membership_l hZF α
  apply wf_no_desc_l hZF hω wf (fn0_of_function_l (ZF.modelsKP hZF) gf)
  intro i j a b succ ha hb
  obtain ⟨_, s, hs, sa⟩ := (read i a).mp ha
  obtain ⟨_, t, ht, tb⟩ := (read j b).mp hb
  exact (edges b a).mpr ⟨gf.output_mem_of_pairMember hb, gf.output_mem_of_pairMember ha,
    rank.decrease s t a b sa tb (next i j s t succ hs ht)⟩

theorem tree_rank_l {ω X F T : M.Domain} (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T)
    (no : ∀ f, M.IsSetFunctionFromTo I f ω X → ¬ Branch_d F T f) :
    ∃ α H, Cg_rank_d ω X T α H := by
  obtain ⟨E, edges⟩ := tree_edges_l I hZF ω T
  obtain ⟨α, H, ha, fn, _, rank⟩ := wr_exists_l I hZF
    (tree_wf_dc_l I hZF hw dc space tree edges no)
  have decrease s t a b (hs : Rd_entry_d s a H) (ht : Rd_entry_d t b H)
      (step : Tb_step_d ω X s t) : M.mem b a := by
    have hsT := fn.input_mem_of_pairMember hs
    have htT := fn.input_mem_of_pairMember ht
    exact ((rank.2.2 s a hs).2 b).mpr ⟨t, b, htT, (edges.2 s t).mpr
      ⟨hsT, htT, (tb_step_l hZF hw space (tree.1 s hsT) (tree.1 t htT)).mp step⟩, ht, Or.inl rfl⟩
  exact ⟨α, H, ha, fn0_of_function_l (ZF.modelsKP hZF) fn, decrease,
    tb_rank_prefix_l hZF hw space tree ha (fn0_of_function_l (ZF.modelsKP hZF) fn) decrease⟩

theorem Cg_rank_d.no_branch_l {ω X F T α H f : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (rank : Cg_rank_d ω X T α H)
    (ff : M.IsSetFunctionFromTo I f ω X) : ¬ Branch_d F T f := by
  intro branch
  obtain ⟨E, edges⟩ := tree_edges_l I hZF ω T
  obtain ⟨G, fn, chain⟩ := tree_branch_desc_l I hZF hw space ff branch edges
  apply rank.no_chain_l hZF hw fn
  intro i j s t succ hs ht
  exact (tb_step_l hZF hw space (tree.1 s (fn.bound_l hs).2)
    (tree.1 t (fn.bound_l ht).2)).mpr (((edges.2 s t).mp (chain i j s t succ hs ht)).2.2)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 秩树任意非空内部节点集都有不能真延长的节点

将该集合的实际秩值在秩序数中分离，取内部最小元。
结论只要求 ZF；不把外部节点类当作可取最小元的集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem Cg_rank_d.minimal_l {ω X R α F Q : M.Domain} (rank : Cg_rank_d ω X R α F)
    (sub : M.MemberSubset Q R) (ne : ∃ h, M.mem h Q) :
    ∃ s, M.mem s Q ∧ ∀ t, M.mem t Q → M.MemberSubset s t → s = t := by
  classical
  let ρ : Env M 2 := ⟨fun i => [Q,F].get i,fun _ => Q⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∃ h ∈ ⌜(.bound 1 : Term 3)⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(h,⌜(.newest : Term 3)⌝ₛ,⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have sat β : φ.denote ρ β ↔ ∃ h, M.mem h Q ∧ Rd_entry_d h β F := by
    simp only [UnarySchema.denote,φ,Formula.satisfies_existsMem_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨A,read⟩ := ZF.separation_exists_d hZF φ ρ α
  have values β := (read β).trans (and_congr_right fun _ => sat β)
  obtain ⟨s₀,hs₀⟩ := ne
  obtain ⟨β₀,hβ₀,sβ₀⟩ := rank.function.2.1 s₀ (sub s₀ hs₀)
  obtain ⟨β,hβ,least⟩ := rank.ordinal.wellOrder.least A (fun β hb => ((values β).mp hb).1)
    ⟨β₀,(values β₀).mpr ⟨hβ₀,s₀,hs₀,sβ₀⟩⟩
  obtain ⟨hβα,s,hs,sβ⟩ := (values β).mp hβ
  refine ⟨s,hs,fun t ht st => ?_⟩
  by_cases eq : s = t
  · exact eq
  · obtain ⟨γ,hγα,tγ⟩ := rank.function.2.1 t (sub t ht)
    have lower := rank.proper s t β γ sβ tγ st eq
    rcases least γ ((values γ).mpr ⟨hγα,t,ht,tγ⟩) with eq | upper
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) γ (hZF.1.eq_of_same_members β γ eq ▸ lower)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) β ((rank.ordinal.mem hβα).transitive γ lower β upper)).elim

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可数前缀树的内部良基性

非空无死节点树用最小子编号生成分支；因此无分支与反向子边内部良基等价。
全程在 ZF 内选择自然数最小元，不假设模型外良基，也不调用依赖选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem tree_pruned_branch_l (hZF : M.Models ZF) {ω A B T} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (ht : Tree_d A T)
    (hne : ∃ s, M.mem s T) (hs : ∀ s, M.mem s T → ∃ t, M.mem t T ∧ Step_d I ω s t) :
    ∃ f, M.mem f B ∧ Branch_d A T f := by
  obtain ⟨E, he⟩ := ha
  obtain ⟨R, hr⟩ := tree_edges_l I hZF ω T
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push E).push T
  let φ : BinarySchema 3 := { body := .conj (.mem .newest (.bound 2)) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))
    (nj_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))) }
  have hp s t : φ.denote ρ s t ↔ M.mem t T ∧ ∃ j, M.PairMember I t j E ∧ Nj_d I R E T s j := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, nj_sat_l I hZF.1]; rfl
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := T)
    (by
      intro s hsT
      obtain ⟨t, htT, hst⟩ := hs s hsT
      obtain ⟨j, hj⟩ := nj_exists_l I hZF he.1 ⟨t, ht.1 t htT, (hr.2 s t).mpr ⟨hsT, htT, hst⟩, htT⟩
      obtain ⟨u, hu, _, huj⟩ := hj.1
      exact ⟨u, (hp s u).mpr ⟨hu, j, huj, hj⟩⟩)
    (by
      intro s _ t u ht' hu'
      obtain ⟨_, j, htj, hj⟩ := (hp s t).mp ht'
      obtain ⟨_, k, huk, hk⟩ := (hp s u).mp hu'
      exact he.2 t u j htj (nj_unique_l I hZF.1 (hB.1.isOrdinal (ZF.modelsKP hZF)) he.1 hk hj ▸ huk))
    (fun s t _ ht' => ((hp s t).mp ht').1)
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  have hzA := (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  have hzT := hne.elim fun s hs => ht.2 s hs z hzA (fun p hp => (hz p hp).elim)
  obtain ⟨f, hff, path⟩ := ds_path_l I hZF hB.1 (fun s hs => (hA s).mp (ht.1 s hs)) hf hz hzT (by
    intro s t hst
    obtain ⟨_, j, htj, hj⟩ := (hp s t).mp ((ef s t).mp hst).2
    obtain ⟨u, _, hus, huj⟩ := hj.1
    exact he.2 u t j huj htj ▸ ((hr.2 s u).mp hus).2.2)
  refine ⟨f, (hB.2 f).mpr hff, (tree_branch_l I hZF hB.1 hA hff).mpr ?_⟩
  intro n hn
  obtain ⟨s, hs, hsf, hsub⟩ := path n hn
  exact ⟨s, hs, (ds_restrict_iff_l I hsf hff.1).mpr hsub⟩

theorem tree_wf_of_no_branch_l (hZF : M.Models ZF) {ω A B T R} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (ht : Tree_d A T)
    (hr : Edge_d I ω T R) (hn : ∀ f, M.mem f B → ¬ Branch_d A T f) : Wf_rel_d T R := by
  classical
  intro Q hQT hQ
  apply Classical.byContradiction
  intro hmin
  have next q (hq : M.mem q Q) : ∃ v, M.mem v Q ∧ Step_d I ω q v := by
    apply Classical.byContradiction
    intro h
    exact hmin ⟨q, hq, fun v hv hvr => h ⟨v, hv, ((hr.2 q v).mp hvr).2.2⟩⟩
  obtain ⟨P, hP⟩ := ktree_exists_l (ZF.modelsKP hZF) A Q
  have sub : M.MemberSubset P T := fun s hs => ((hP s).mp hs).2.elim fun q hq =>
    ht.2 q (hQT q hq.1) s ((hP s).mp hs).1 hq.2
  have tree : Tree_d A P := ⟨fun s hs => ((hP s).mp hs).1, fun s hs t ht hts => by
    obtain ⟨_, q, hq, hsq⟩ := (hP s).mp hs
    exact (hP t).mpr ⟨ht, q, hq, fun p hp => hsq p (hts p hp)⟩⟩
  have pruned s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Step_d I ω s t := by
    obtain ⟨hsA, q, hqQ, hsq⟩ := (hP s).mp hs
    obtain ⟨v, hvQ, hqv⟩ := next q hqQ
    obtain ⟨n, hn, hsf⟩ := (hA s).mp hsA
    obtain ⟨l, hl, hqf⟩ := (hA q).mp (ht.1 q (hQT q hqQ))
    obtain ⟨m, hm, hvf⟩ := (hA v).mp (ht.1 v (hQT v hvQ))
    obtain ⟨hml, hqv⟩ := (tree_step_iff_l I hZF hB.1 hl hm hqf hvf).mp hqv
    have hnl : M.MemberSubset n l := fun i hi => by
      obtain ⟨a, _, hia⟩ := hsf.2.2 i hi
      exact hqf.input_mem_of_pairMember (hia.elim fun p hp => ⟨p, hp.1, hsq p hp.2⟩)
    have hnm : M.mem n m := by
      rcases (hB.1.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn l hl with e | e | e
      · exact (hZF.1.eq_of_same_members n l e).symm ▸ hml.predecessor_mem
      · exact (hml n).mpr (Or.inl e)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (hnl l e)).elim
    obtain ⟨u, hu, huω⟩ := hB.1.1.2 n hn
    have hum : M.MemberSubset u m := fun i hi => ((hu i).mp hi).elim
      (fun hi => (hml i).mpr (Or.inl (hnl i hi))) (fun e => (hZF.1.eq_of_same_members i n e).symm ▸ hnm)
    obtain ⟨t, htv⟩ := ZF.exists_restriction hZF I v u
    have htf := htv.isSetFunctionFromTo hvf hum
    have hst := ds_prefix_mono_l I hsf htf.1 ((ds_restrict_iff_l I hsf hvf.1).mpr
      (fun p hp => hqv p (hsq p hp))) htv (fun i hi => (hu i).mpr (Or.inl hi))
    exact ⟨t, (hP t).mpr ⟨(hA t).mpr ⟨u, huω, htf⟩, v, hvQ, (ds_restrict_iff_l I htf hvf.1).mp htv⟩,
      (tree_step_iff_l I hZF hB.1 hn huω hsf htf).mpr ⟨hu, hst⟩⟩
  have hne : ∃ s, M.mem s P := hQ.elim fun q hq => ⟨q, (hP q).mpr ⟨ht.1 q (hQT q hq), q, hq, fun _ => id⟩⟩
  obtain ⟨f, hf, hbranch⟩ := tree_pruned_branch_l I hZF hB hA ha tree hne pruned
  exact hn f hf (fun s hs hsf => sub s (hbranch s hs hsf))

theorem tree_wf_iff_l (hZF : M.Models ZF) {ω A B T R} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (ht : Tree_d A T) (hr : Edge_d I ω T R) :
    Wf_rel_d T R ↔ ∀ f, M.mem f B → ¬ Branch_d A T f := by
  refine ⟨fun hw f hf hb => ?_, tree_wf_of_no_branch_l I hZF hB hA ha ht hr⟩
  obtain ⟨G, hg, desc⟩ := tree_branch_desc_l I hZF hB.1 hA ((hB.2 f).mp hf) hb hr
  exact wf_no_desc_l hZF hB.1 hw hg desc

end YesMetaZFC.SetTheory.Descriptive
