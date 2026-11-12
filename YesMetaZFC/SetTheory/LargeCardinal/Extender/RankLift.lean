import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

/-! # 原所属短扩展器公式在严格极限秩段中的保持

载体与测度图属于秩段时，测度候选的全部子集以及有限函数都回到秩段。
可数共同纤维的见证是 ω→κ 的实际图，也由同一有界关系闭包回收。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

omit hZF in
private theorem el_maximal_rank_l {X α V : M.Domain} (hX : M.TransitiveSet X)
    (hV : M.mem V X) (rank : Vr_d X α V) (nx : Nonempty {x // M.mem x X})
    (nv : Nonempty {x // M.mem x V}) (D U : (rt_model_l V nv).Domain)
    (maximal : Maximal_d (ℳ := rt_model_l X nx)
      ⟨D.val, hX V hV D.val D.property⟩ ⟨U.val, hX V hV U.val U.property⟩) :
    Maximal_d (ℳ := rt_model_l V nv) D U := by
  let N := rt_model_l X nx
  let Q := rt_model_l V nv
  have ht := rank.transitive_l hX hV
  let l (a : Q.Domain) : N.Domain := ⟨a.val, hX V hV a.val a.property⟩
  have sub (A B : Q.Domain) : Subset_d (ℳ := N) (l A) (l B) ↔ Subset_d (ℳ := Q) A B :=
    ⟨fun h x hx => h (l x) hx, fun h x hx => h ⟨x.val, ht A.val A.property x.val hx⟩ hx⟩
  refine ⟨⟨fun A hA => (sub A D).mp (maximal.1.1 (l A) hA), maximal.1.2.1,
    fun A B hA ab bd => maximal.1.2.2.1 (l A) (l B) hA ((sub A B).mpr ab) ((sub B D).mpr bd), ?_⟩, ?_, ?_⟩
  · intro A B hA hB
    obtain ⟨C, hC, ca, cb⟩ := maximal.1.2.2.2 (l A) (l B) hA hB
    let c : Q.Domain := ⟨C.val, ht U.val U.property C.val hC⟩
    exact ⟨c, hC, (sub c A).mp ca, (sub c B).mp cb⟩
  · intro A hA
    obtain ⟨x, hx⟩ := maximal.2.1 (l A) hA
    exact ⟨⟨x.val, ht A.val A.property x.val hx⟩, hx⟩
  · intro G filter proper ug
    have owned (A : N.Domain) (hA : Subset_d (ℳ := N) A (l D)) : M.mem A.val V :=
      rank.subset_mem_l hX hV D.property A.property (fun x hx => hA ⟨x, hX A.val A.property x hx⟩ hx)
    have full : IsFilter_d (ℳ := N) (l D) (l G) := by
      refine ⟨fun A hA => ?_, filter.2.1, fun A B hA ab bd => ?_, fun A B hA hB => ?_⟩
      · let a : Q.Domain := ⟨A.val, ht G.val G.property A.val hA⟩
        exact (sub a D).mpr (filter.1 a hA)
      · let a : Q.Domain := ⟨A.val, ht G.val G.property A.val hA⟩
        let b : Q.Domain := ⟨B.val, owned B bd⟩
        exact filter.2.2.1 a b hA ((sub a b).mp ab) ((sub b D).mp bd)
      · let a : Q.Domain := ⟨A.val, ht G.val G.property A.val hA⟩
        let b : Q.Domain := ⟨B.val, ht G.val G.property B.val hB⟩
        obtain ⟨C, hC, ca, cb⟩ := filter.2.2.2 a b hA hB
        exact ⟨l C, hC, (sub C a).mpr ca, (sub C b).mpr cb⟩
    have full_proper : Proper_d (ℳ := N) (l G) := fun A hA => by
      obtain ⟨x, hx⟩ := proper ⟨A.val, ht G.val G.property A.val hA⟩ hA
      exact ⟨l x, hx⟩
    exact (sub G U).mp (maximal.2.2 (l G) full full_proper ((sub U G).mpr ug))

/-- 可数共同纤维原公式的向下保持只需极限秩闭包，不要求背景可数完备性。 -/
theorem ex_countable_rank_l {ω κ K X R α V L F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hV : M.mem V X) (rank : Vr_d X α V)
    (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V) (hL : M.mem L V) (hF : M.mem F V)
    (countable : Formula.satisfies
      (⟨Fin.cases ⟨F, source.transitive V hV F hF⟩ (Fin.cases ⟨L, source.transitive V hV L hL⟩
        (Fin.cases ⟨κ, source.cardinal_mem⟩ (fun _ => ⟨ω, source.omega_mem⟩))), fun _ => ⟨ω, source.omega_mem⟩⟩ :
        Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4) (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest)) :
    ∃ hω : M.mem ω V, Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩))), fun _ => ⟨ω, hω⟩⟩ :
        Env (rt_model_l V ⟨⟨ω, hω⟩⟩) 4) (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest) := by
  have hω := rank.subset_mem_l source.transitive hV hκ source.omega_mem source.below
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hω⟩⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let Q := rt_model_l V nv
  let N := rt_model_l X nx
  have ht := rank.transitive_l source.transitive hV
  have algebra := (source.algebra_l (ZF.modelsKP hZF)).rank_l hZF source.transitive hV rank hα
  let l (x : Q.Domain) : N.Domain := ⟨x.val, source.transitive V hV x.val x.property⟩
  let ρ : Env Q 4 := ⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩))), fun _ => ⟨ω, hω⟩⟩
  let η := image_env_l l ρ
  have old : Formula.satisfies η (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest) :=
    (Formula.closed_env_l _ (by simp -implicitDefEqProofs)
      (by funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i)).mp countable
  refine ⟨hω, ?_⟩
  simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff] at old ⊢
  intro H f levels fiber
  have levels := (ef_levels_relative_l hZF.1 ht algebra nv ..).mp levels
  have fiber := (es_fiber_relative_l (ZF.modelsKP hZF) ht nv ..).mp fiber
  obtain ⟨g, hg⟩ := old (l H) (l f)
    ((ef_levels_relative_l hZF.1 source.transitive (source.algebra_l (ZF.modelsKP hZF)) nx ..).mpr levels)
    ((es_fiber_relative_l (ZF.modelsKP hZF) source.transitive nx ..).mpr fiber)
  have hg := (ef_fiber_relative_l hZF.1 source.transitive nx ..).mp hg
  have owned := rank.relation_mem_l source.transitive hV hα hω hκ g.property hg.1.1
  exact ⟨⟨g.val, owned⟩, (ef_fiber_relative_l hZF.1 ht nv ..).mpr hg⟩

/-- 扩展器的全部原参数位于严格极限秩段时，原短扩展器判断在该秩段内成立。 -/
theorem It_local_d.rank_l {ω κ K X R α V S L F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hV : M.mem V X) (rank : Vr_d X α V)
    (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V) (hL : M.mem L V) (hF : M.mem F V)
    (code : ∃ c, Smem_d I c V S) (loc : It_local_d I ω X R κ L F) : It_local_d I ω V S κ L F := by
  apply (it_local_mem_l I code).mpr
  have local_copy := (it_local_mem_l I source.code).mp loc
  obtain ⟨_, _, _, _, old_countable⟩ := local_copy
  obtain ⟨hω, countable⟩ := ex_countable_rank_l hZF source hV rank hα hκ hL hF
    ((Formula.satisfies_conj_iff _ _ _).mp old_countable).2
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hω⟩⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let Q := rt_model_l V nv
  let N := rt_model_l X nx
  have ht := rank.transitive_l source.transitive hV
  have algebra := (source.algebra_l (ZF.modelsKP hZF)).rank_l hZF source.transitive hV rank hα
  have he := rt_model_ext_l hZF.1 ht nv
  have he' := rt_model_ext_l hZF.1 source.transitive nx
  let J := rt_pair_l ht nv hZF.1 algebra.pair
  let J' := rt_pair_l source.transitive nx hZF.1 (source.algebra_l (ZF.modelsKP hZF)).pair
  let l (x : Q.Domain) : N.Domain := ⟨x.val, source.transitive V hV x.val x.property⟩
  let w : Q.Domain := ⟨ω, hω⟩
  let k : Q.Domain := ⟨κ, hκ⟩
  let z : Q.Domain := ⟨L, hL⟩
  let e : Q.Domain := ⟨F, hF⟩
  let ρ : Env Q 4 := ⟨Fin.cases e (Fin.cases z (Fin.cases k (fun _ => w))), fun _ => w⟩
  have fn (A B f : Q.Domain) : Fn0_d A B f ↔ Fn0_d (l A) (l B) (l f) :=
    (rt_fn_l ht nv hZF.1 A B f).trans (rt_fn_l source.transitive nx hZF.1 (l A) (l B) (l f)).symm
  have entry (a b f : Q.Domain) : Rd_entry_d a b f ↔ Rd_entry_d (l a) (l b) (l f) :=
    (rt_entry_l ht nv hZF.1 a b f).trans (rt_entry_l source.transitive nx hZF.1 (l a) (l b) (l f)).symm
  have cp (m n K q s t : Q.Domain) : Cp0_d m n K q s t ↔ Cp0_d (l m) (l n) (l K) (l q) (l s) (l t) :=
    (rt_cp_l ht nv hZF.1 m n K q s t).trans
      (rt_cp_l source.transitive nx hZF.1 (l m) (l n) (l K) (l q) (l s) (l t)).symm
  have sub (A B : Q.Domain) : Q.MemberSubset A B ↔ N.MemberSubset (l A) (l B) :=
    ⟨fun h x hx => h ⟨x.val, ht A.val A.property x.val hx⟩ hx, fun h x hx => h (l x) hx⟩
  have delta {d} (φ : Formula 1 d) (hd : φ.IsDelta0) (η : Env Q d) :
      Formula.satisfies η φ ↔ Formula.satisfies (image_env_l l η) φ :=
    (rt_model_delta_l ht nv hd η).trans (rt_model_delta_l source.transitive nx hd (image_env_l l η)).symm
  obtain ⟨P, hP, seq⟩ := source.rank_sequence_l (ZF.modelsKP hZF) hV rank hα hω hκ
  have finite (n s : N.Domain) (hn : M.mem n.val ω) (hf : Fn0_d n (l k) s) : M.mem s.val V :=
    ht P hP s.val ((seq s.val).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF)
      ((rt_fn_l source.transitive nx hZF.1 n (l k) s).mp hf)⟩)
  have space (n D : Q.Domain) (hn : Q.mem n w) (hd : ∀ s, Q.mem s D ↔ Fn0_d n k s) :
      ∀ s : N.Domain, N.mem s (l D) ↔ Fn0_d (l n) (l k) s := fun s =>
    ⟨fun hs => (fn n k ⟨s.val, ht D.val D.property s.val hs⟩).mp ((hd _).mp hs),
      fun hs => (hd ⟨s.val, finite (l n) s hn hs⟩).mpr ((fn n k _).mpr hs)⟩
  obtain ⟨_, _, _, _, old⟩ := (it_local_mem_l I source.code).mp loc
  have old := ((Formula.satisfies_conj_iff _ _ _).mp old).1
  have old : Formula.satisfies (image_env_l l ρ) (ex_pre_m (.bound 3) (.bound 2) (.bound 1) .newest) :=
    (Formula.closed_env_l _ (by simp -implicitDefEqProofs)
      (by funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i)).mp old
  simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isCardinal_iff J' he', Formula.satisfies_mem_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isFunction_iff J' he', em_family_sat_l he', es_coherent_sat_l J' he',
    ex_complete_sat_l he', ea_atoms_sat_l he', en_normal_sat_l he', ex_principal_sat_l he', ex_nonprincipal_sat_l he'] at old
  obtain ⟨_, cardinal, uncountable, length, above, graph, measures, coherent, complete, atoms, normal, principal, nonprincipal⟩ := old
  refine ⟨hω, hκ, hL, hF, (Formula.satisfies_conj_iff _ _ _).mpr ⟨?_, countable⟩⟩
  change Formula.satisfies ρ (ex_pre_m (.bound 3) (.bound 2) (.bound 1) .newest)
  simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isCardinal_iff J he, Formula.satisfies_mem_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isFunction_iff J he, em_family_sat_l he, es_coherent_sat_l J he,
    ex_complete_sat_l he, ea_atoms_sat_l he, en_normal_sat_l he, ex_principal_sat_l he, ex_nonprincipal_sat_l he]
  refine ⟨rt_omega_l ht nv hZF.1 w source.omega, ?_, uncountable,
    rt_ordinal_l ht nv z ((rt_ordinal_iff_l source.transitive nx (ZF.modelsKP hZF) (l z)).mp length), above,
    (rt_function_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) algebra.pair e).mpr
      ((rt_function_l source.transitive nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (source.algebra_l (ZF.modelsKP hZF)).pair (l e)).mp graph),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rt_cardinal_restrict_l source.transitive nx hZF.1 (source.algebra_l (ZF.modelsKP hZF)).pair
      (ZF.modelsKP hZF) ht nv algebra.pair (source.transitive V hV) k cardinal
  · refine ⟨fun n a hn ha => ?_, fun a U V hu hv => ?_, fun a U hu => ?_⟩
    · obtain ⟨U, hu⟩ := measures.total (l n) (l a) hn ((fn n z a).mp ha)
      have hU := (rd_entry_transitive_l ht hF ((rt_entry_l source.transitive nx hZF.1 ..).mp hu)).2
      exact ⟨⟨U.val, hU⟩, (entry a _ e).mpr hu⟩
    · exact Subtype.ext (congrArg (fun x : N.Domain => x.val)
        (measures.function (l a) (l U) (l V) ((entry a U e).mp hu) ((entry a V e).mp hv)))
    · obtain ⟨n, D, hn, ha, hd, maximal⟩ := measures.measure (l a) (l U) ((entry a U e).mp hu)
      have hD := rank.subset_mem_l source.transitive hV hP D.property (fun s hs =>
        (seq s).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF)
          ((rt_fn_l source.transitive nx hZF.1 n (l k) ⟨s, source.transitive D.val D.property s hs⟩).mp ((hd _).mp hs))⟩)
      let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
      let D' : Q.Domain := ⟨D.val, hD⟩
      exact ⟨n', D', hn, (fn n' z a).mpr ha, fun s => (hd (l s)).trans (fn n' k s).symm,
        el_maximal_rank_l source.transitive hV rank nx nv D' U maximal⟩
  · intro m n q a b U W A hm hn hq ha hb hav hbu all
    obtain ⟨Z, pull, iff⟩ := coherent (l m) (l n) (l q) (l a) (l b) (l U) (l W) (l A) hm hn
      ((fn m n q).mp hq) ((fn n z a).mp ha) ((cp m n z q a b).mp hb)
      ((entry a W e).mp hav) ((entry b U e).mp hbu)
      (fun t ht' => (fn m k ⟨t.val, ht A.val A.property t.val ht'⟩).mp (all _ ht'))
    have hZ := rank.subset_mem_l source.transitive hV hP Z.property (fun s hs =>
      (seq s).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF)
        ((rt_fn_l source.transitive nx hZF.1 (l n) (l k) ⟨s, source.transitive Z.val Z.property s hs⟩).mp
          ((pull ⟨s, source.transitive Z.val Z.property s hs⟩).mp hs).1)⟩)
    refine ⟨⟨Z.val, hZ⟩, fun s => ?_, iff⟩
    refine (pull (l s)).trans (and_congr (fn n k s).symm ?_)
    exact ⟨fun ⟨t, ht', comp⟩ => ⟨⟨t.val, ht A.val A.property t.val ht'⟩, ht', (cp m n k q s _).mpr comp⟩,
      fun ⟨t, ht', comp⟩ => ⟨l t, ht', (cp m n k q s t).mp comp⟩⟩
  · intro n a U D ha hu hd μ hμ f hf
    obtain ⟨m, _, hm, ha', _⟩ := measures.measure (l a) (l U) ((entry a U e).mp hu)
    have eq := ha'.domain_eq_l he' ((fn n z a).mp ha)
    have hno : Q.mem n w := by change N.mem (l n) (l w); exact eq ▸ hm
    obtain ⟨B, hB, spec⟩ := complete (l n) (l a) (l U) (l D) ((fn n z a).mp ha)
      ((entry a U e).mp hu) (space n D hno hd) (l μ) hμ (l f) ((fn μ U f).mp hf)
    let B' : Q.Domain := ⟨B.val, ht U.val U.property B.val hB⟩
    refine ⟨B', hB, fun x => (spec (l x)).trans (and_congr Iff.rfl ?_)⟩
    let η : Env Q 4 := ⟨Fin.cases x (Fin.cases f (Fin.cases U (fun _ => μ))), fun _ => μ⟩
    exact ((ed_all_sat_l he η (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
      ((delta (ed_all_m (.bound 3) (.bound 2) (.bound 1) .newest) (ed_all_delta_l ..) η).trans
        (ed_all_sat_l he' _ _ _ _ _))).symm
  · intro p n a U i r α β hn ha hu hi hr
    obtain ⟨T, spec, iff⟩ := atoms p (l n) (l a) (l U) (l i) (l r) (l α) (l β) hn
      ((fn n z a).mp ha) ((entry a U e).mp hu) ((entry i α a).mp hi) ((entry r β a).mp hr)
    have hT := rank.subset_mem_l source.transitive hV hP T.property (fun s hs =>
      (seq s).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF)
        ((rt_fn_l source.transitive nx hZF.1 (l n) (l k) ⟨s, source.transitive T.val T.property s hs⟩).mp
          ((spec ⟨s, source.transitive T.val T.property s hs⟩).mp hs).1)⟩)
    refine ⟨⟨T.val, hT⟩, fun s => (spec (l s)).trans (and_congr (fn n k s).symm ?_), ?_⟩
    · let η : Env Q 4 := ⟨Fin.cases s (Fin.cases r (Fin.cases i (fun _ => k))), fun _ => k⟩
      exact ((ea_test_sat_l he η p (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((delta (ea_test_m p (.bound 3) (.bound 2) (.bound 1) .newest) (ea_test_delta_l ..) η).trans
          (ea_test_sat_l he' _ _ _ _ _ _))).symm
    · cases p with
      | false => exact iff
      | true => exact iff.trans ⟨fun h => Subtype.ext (congrArg (fun x : N.Domain => x.val) h), congrArg l⟩
  · intro n a U D f i α A hn ha hu hd hf hi hA reg
    obtain ⟨m, b, W, β, B, hm, succ, fb, ab, last, lt, hbW, hBW, graph⟩ := normal
      (l n) (l a) (l U) (l D) (l f) (l i) (l α) (l A) hn ((fn n z a).mp ha)
      ((entry a U e).mp hu) (space n D hn hd) ((fn D k f).mp hf) ((entry i α a).mp hi) hA (fun s hs x y hfx hiy => by
        have hsV := ht A.val A.property s.val hs
        have hx := (rd_entry_transitive_l ht f.property ((rt_entry_l source.transitive nx hZF.1 ..).mp hfx)).2
        have hy := (rd_entry_transitive_l ht hsV ((rt_entry_l source.transitive nx hZF.1 ..).mp hiy)).2
        exact reg ⟨s.val, hsV⟩ hs ⟨x.val, hx⟩ ⟨y.val, hy⟩ ((entry _ _ f).mpr hfx) ((entry i _ _).mpr hiy))
    have bw := rd_entry_transitive_l ht hF ((rt_entry_l source.transitive nx hZF.1 ..).mp hbW)
    let m' : Q.Domain := ⟨m.val, ht ω hω m.val hm⟩
    let b' : Q.Domain := ⟨b.val, bw.1⟩
    let W' : Q.Domain := ⟨W.val, bw.2⟩
    let β' : Q.Domain := ⟨β.val, ht α.val α.property β.val lt⟩
    let B' : Q.Domain := ⟨B.val, ht W.val bw.2 B.val hBW⟩
    refine ⟨m', b', W', β', B', hm, (rt_successor_l ht nv hZF.1 m' n).mpr
      ((rt_successor_l source.transitive nx hZF.1 m (l n)).mp succ), (fn m' z b').mpr fb,
      (sub a b').mpr ab, (entry n β' b').mpr last, lt, (entry b' W' e).mpr hbW, hBW, fun s hs => ?_⟩
    let η : Env Q 5 := ⟨Fin.cases s (Fin.cases f (Fin.cases A (Fin.cases k (fun _ => n)))), fun _ => n⟩
    exact ((en_graph_sat_l he η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
      ((delta (en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) (en_graph_delta_l ..) η).trans
        (en_graph_sat_l he' _ _ _ _ _ _))).mpr (graph (l s) hs)
  · intro n a U hn ha hu A
    refine (principal (l n) (l a) (l U) hn ((fn n k a).mp ha) ((entry a U e).mp hu) (l A)).trans (and_congr ?_ Iff.rfl)
    exact ⟨fun all s hs => (fn n k s).mpr (all (l s) hs),
      fun all s hs => (fn n k ⟨s.val, ht A.val A.property s.val hs⟩).mp (all _ hs)⟩
  · intro a U i α hu hi hα x s single
    apply nonprincipal (l a) (l U) (l i) (l α) ((entry a U e).mp hu) ((entry i α a).mp hi) hα (l x) (l s)
    intro y
    refine ⟨fun hy => ?_, fun eq => ?_⟩
    · exact Subtype.ext (congrArg (fun x : Q.Domain => x.val) ((single ⟨y.val, ht s.val s.property y.val hy⟩).mp hy))
    · cases eq; exact (single x).mpr rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 严格极限秩段中的短扩展器向上保持

所有待检验的图都由原参数给出秩界：有限支撑、κ 以下的函数、测度候选
及可数层族均回到原秩段。原内部短扩展器公式因此也在大源中成立。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

omit hZF in
private theorem el_maximal_up_l {X α V : M.Domain} (hX : M.TransitiveSet X)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (nx : Nonempty {x // M.mem x X}) (nv : Nonempty {x // M.mem x V}) (D U : (rt_model_l V nv).Domain)
    (maximal : Maximal_d (ℳ := rt_model_l V nv) D U) :
    Maximal_d (ℳ := rt_model_l X nx) ⟨D.val, hX V hV D.val D.property⟩ ⟨U.val, hX V hV U.val U.property⟩ := by
  let N := rt_model_l X nx
  let Q := rt_model_l V nv
  have ht := rank.transitive_l hX hV
  let l (a : Q.Domain) : N.Domain := ⟨a.val, hX V hV a.val a.property⟩
  have sub (A B : Q.Domain) : Subset_d (ℳ := Q) A B ↔ Subset_d (ℳ := N) (l A) (l B) :=
    ⟨fun h x hx => h ⟨x.val, ht A.val A.property x.val hx⟩ hx, fun h x hx => h (l x) hx⟩
  have own (A : N.Domain) (hA : Subset_d (ℳ := N) A (l D)) : M.mem A.val V :=
    rank.subset_mem_l hX hV D.property A.property (fun x hx => hA ⟨x, hX A.val A.property x hx⟩ hx)
  refine ⟨⟨fun A hA => (sub ⟨A.val, ht U.val U.property A.val hA⟩ D).mp (maximal.1.1 _ hA),
    maximal.1.2.1, ?_, ?_⟩, ?_, ?_⟩
  · intro A B hA ab bd
    let a : Q.Domain := ⟨A.val, ht U.val U.property A.val hA⟩
    let b : Q.Domain := ⟨B.val, own B bd⟩
    exact maximal.1.2.2.1 a b hA ((sub a b).mpr ab) ((sub b D).mpr bd)
  · intro A B hA hB
    let a : Q.Domain := ⟨A.val, ht U.val U.property A.val hA⟩
    let b : Q.Domain := ⟨B.val, ht U.val U.property B.val hB⟩
    obtain ⟨C, hC, ca, cb⟩ := maximal.1.2.2.2 a b hA hB
    exact ⟨l C, hC, (sub C a).mp ca, (sub C b).mp cb⟩
  · intro A hA
    obtain ⟨x, hx⟩ := maximal.2.1 ⟨A.val, ht U.val U.property A.val hA⟩ hA
    exact ⟨l x, hx⟩
  · intro G filter proper ug
    have hG := rank.subsets_mem_l hX hV hα D.property G.property (fun A hA x hx =>
      filter.1 ⟨A, hX G.val G.property A hA⟩ hA ⟨x, hX A (hX G.val G.property A hA) x hx⟩ hx)
    let g : Q.Domain := ⟨G.val, hG⟩
    have cut : IsFilter_d (ℳ := Q) D g := by
      refine ⟨fun A hA => (sub A D).mpr (filter.1 (l A) hA), filter.2.1,
        fun A B hA ab bd => filter.2.2.1 (l A) (l B) hA ((sub A B).mp ab) ((sub B D).mp bd), ?_⟩
      intro A B hA hB
      obtain ⟨C, hC, ca, cb⟩ := filter.2.2.2 (l A) (l B) hA hB
      let c : Q.Domain := ⟨C.val, ht G.val hG C.val hC⟩
      exact ⟨c, hC, (sub c A).mpr ca, (sub c B).mpr cb⟩
    have cp : Proper_d (ℳ := Q) g := fun A hA => by
      obtain ⟨x, hx⟩ := proper (l A) hA
      exact ⟨⟨x.val, ht A.val A.property x.val hx⟩, hx⟩
    exact (sub g U).mp (maximal.2.2 g cut cp ((sub U g).mpr ug))

theorem It_local_d.of_rank_l {ω κ K X R α V S L F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hV : M.mem V X) (rank : Vr_d X α V)
    (hα : M.IsLimitOrdinal α) (code : ∃ c, Smem_d I c V S) (loc : It_local_d I ω V S κ L F) : It_local_d I ω X R κ L F := by
  apply (it_local_mem_l I source.code).mpr
  obtain ⟨hω, hκ, hL, hF, old⟩ := (it_local_mem_l I code).mp loc
  have hx := source.transitive
  have ht := rank.transitive_l hx hV
  have algebra := (source.algebra_l (ZF.modelsKP hZF)).rank_l hZF hx hV rank hα
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hω⟩⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let Q := rt_model_l V nv
  let N := rt_model_l X nx
  let l (x : Q.Domain) : N.Domain := ⟨x.val, hx V hV x.val x.property⟩
  let w : Q.Domain := ⟨ω, hω⟩
  let k : Q.Domain := ⟨κ, hκ⟩
  let z : Q.Domain := ⟨L, hL⟩
  let e : Q.Domain := ⟨F, hF⟩
  let ρ : Env Q 4 := ⟨Fin.cases e (Fin.cases z (Fin.cases k (fun _ => w))), fun _ => w⟩
  have he := rt_model_ext_l hZF.1 ht nv
  have he' := rt_model_ext_l hZF.1 hx nx
  let J := rt_pair_l ht nv hZF.1 algebra.pair
  let J' := rt_pair_l hx nx hZF.1 (source.algebra_l (ZF.modelsKP hZF)).pair
  have fn (A B f : Q.Domain) : Fn0_d A B f ↔ Fn0_d (l A) (l B) (l f) :=
    (rt_fn_l ht nv hZF.1 A B f).trans (rt_fn_l hx nx hZF.1 (l A) (l B) (l f)).symm
  have entry (a b f : Q.Domain) : Rd_entry_d a b f ↔ Rd_entry_d (l a) (l b) (l f) :=
    (rt_entry_l ht nv hZF.1 a b f).trans (rt_entry_l hx nx hZF.1 (l a) (l b) (l f)).symm
  have cp (m n K q s t : Q.Domain) : Cp0_d m n K q s t ↔ Cp0_d (l m) (l n) (l K) (l q) (l s) (l t) :=
    (rt_cp_l ht nv hZF.1 m n K q s t).trans (rt_cp_l hx nx hZF.1 (l m) (l n) (l K) (l q) (l s) (l t)).symm
  have sub (A B : Q.Domain) : Q.MemberSubset A B ↔ N.MemberSubset (l A) (l B) :=
    ⟨fun h x hx => h ⟨x.val, ht A.val A.property x.val hx⟩ hx, fun h x hx => h (l x) hx⟩
  have delta {d} (φ : Formula 1 d) (hd : φ.IsDelta0) (η : Env Q d) :
      Formula.satisfies η φ ↔ Formula.satisfies (image_env_l l η) φ :=
    (rt_model_delta_l ht nv hd η).trans (rt_model_delta_l hx nx hd (image_env_l l η)).symm
  have own (A B f : N.Domain) (hA : M.mem A.val V) (hB : M.mem B.val V) (hf : Fn0_d A B f) : M.mem f.val V :=
    rank.relation_mem_l hx hV hα hA hB f.property ((rt_fn_l hx nx hZF.1 A B f).mp hf).1
  have endpoints (a U : N.Domain) (haU : Rd_entry_d a U (l e)) :=
    rd_entry_transitive_l ht hF ((rt_entry_l hx nx hZF.1 a U (l e)).mp haU)
  obtain ⟨P, hP, seq⟩ := source.rank_sequence_l (ZF.modelsKP hZF) hV rank hα hω hκ
  have finite (n s : N.Domain) (hn : M.mem n.val ω) (hf : Fn0_d n (l k) s) : M.mem s.val V :=
    ht P hP s.val ((seq s.val).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF) ((rt_fn_l hx nx hZF.1 n (l k) s).mp hf)⟩)
  have family_owned (n A : N.Domain) (hn : M.mem n.val ω) (all : ∀ s, N.mem s A → Fn0_d n (l k) s) : M.mem A.val V :=
    rank.subset_mem_l hx hV hP A.property (fun s hs => (seq s).mpr ⟨n.val, hn,
      fn0_function_l (ZF.modelsKP hZF) ((rt_fn_l hx nx hZF.1 n (l k) ⟨s, hx A.val A.property s hs⟩).mp (all _ hs))⟩)
  have space (n D : Q.Domain) (hn : Q.mem n w) (hd : ∀ s, Q.mem s D ↔ Fn0_d n k s) :
      ∀ s : N.Domain, N.mem s (l D) ↔ Fn0_d (l n) (l k) s := fun s =>
    ⟨fun hs => (fn n k ⟨s.val, ht D.val D.property s.val hs⟩).mp ((hd _).mp hs),
      fun hs => (hd ⟨s.val, finite (l n) s hn hs⟩).mpr ((fn n k _).mpr hs)⟩
  obtain ⟨pre, countable⟩ := (Formula.satisfies_conj_iff _ _ _).mp old
  have pre : Formula.satisfies ρ (ex_pre_m (.bound 3) (.bound 2) (.bound 1) .newest) := pre
  simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isCardinal_iff J he, Formula.satisfies_mem_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isFunction_iff J he, em_family_sat_l he, es_coherent_sat_l J he,
    ex_complete_sat_l he, ea_atoms_sat_l he, en_normal_sat_l he, ex_principal_sat_l he, ex_nonprincipal_sat_l he] at pre
  obtain ⟨_, cardinal, uncountable, length, above, graph, measures, coherent, complete, atoms, normal, principal, nonprincipal⟩ := pre
  refine ⟨source.omega_mem, source.cardinal_mem, hx V hV L hL, hx V hV F hF, ?_⟩
  apply (Formula.closed_env_l _ (by simp -implicitDefEqProofs) (ρ := image_env_l l ρ)
    (by funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i)).mp
  apply (Formula.satisfies_conj_iff _ _ _).mpr
  constructor
  · simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isCardinal_iff J' he', Formula.satisfies_mem_iff, Formula.satisfies_isOrdinal_iff,
      Formula.satisfies_isFunction_iff J' he', em_family_sat_l he', es_coherent_sat_l J' he',
      ex_complete_sat_l he', ea_atoms_sat_l he', en_normal_sat_l he', ex_principal_sat_l he', ex_nonprincipal_sat_l he']
    refine ⟨rt_omega_l hx nx hZF.1 (l w) source.omega, ?_, uncountable,
      rt_ordinal_l hx nx (l z) ((rt_ordinal_iff_l ht nv (ZF.modelsKP hZF) z).mp length), above,
      (rt_function_l hx nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (source.algebra_l (ZF.modelsKP hZF)).pair (l e)).mpr
        ((rt_function_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) algebra.pair e).mp graph),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨rt_ordinal_l hx nx (l k) ((rt_ordinal_iff_l ht nv (ZF.modelsKP hZF) k).mp cardinal.1), ?_⟩
      rintro μ hμ ⟨f, hf⟩
      have hμV := ht κ hκ μ.val hμ
      have ff := (rt_bijection_l hx nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (source.algebra_l (ZF.modelsKP hZF)).pair f μ (l k)).mp hf
      have hfV := rank.relation_mem_l hx hV hα hμV hκ f.property (fn0_of_function_l (ZF.modelsKP hZF) ff.1.1).1
      exact cardinal.2 ⟨μ.val, hμV⟩ hμ ⟨⟨f.val, hfV⟩,
        (rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) algebra.pair _ _ k).mpr ff⟩
    · refine ⟨fun n a hn ha => ?_, fun a U W hu hw => ?_, fun a U hu => ?_⟩
      · let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
        let a' : Q.Domain := ⟨a.val, own n (l z) a n'.property hL ha⟩
        obtain ⟨U, hu⟩ := measures.total n' a' hn ((fn n' z a').mpr ha)
        exact ⟨l U, (entry a' U e).mp hu⟩
      · let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
        let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
        let v : Q.Domain := ⟨W.val, (endpoints a W hw).2⟩
        exact congrArg l (measures.function a' u v ((entry a' u e).mpr hu) ((entry a' v e).mpr hw))
      · let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
        let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
        obtain ⟨n, D, hn, ha, hd, maximal⟩ := measures.measure a' u ((entry a' u e).mpr hu)
        exact ⟨l n, l D, hn, (fn n z a').mp ha, space n D hn hd, el_maximal_up_l hx hV rank hα nx nv D u maximal⟩
    · intro m n q a b U W A hm hn hq ha hb hav hbu all
      let m' : Q.Domain := ⟨m.val, ht ω hω m.val hm⟩
      let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
      let q' : Q.Domain := ⟨q.val, own m n q m'.property n'.property hq⟩
      let a' : Q.Domain := ⟨a.val, (endpoints a W hav).1⟩
      let b' : Q.Domain := ⟨b.val, (endpoints b U hbu).1⟩
      let u : Q.Domain := ⟨U.val, (endpoints b U hbu).2⟩
      let v : Q.Domain := ⟨W.val, (endpoints a W hav).2⟩
      let A' : Q.Domain := ⟨A.val, family_owned m A hm all⟩
      obtain ⟨B, pull, decide⟩ := coherent m' n' q' a' b' u v A' hm hn ((fn m' n' q').mpr hq)
        ((fn n' z a').mpr ha) ((cp m' n' z q' a' b').mpr hb) ((entry a' v e).mpr hav) ((entry b' u e).mpr hbu)
        (fun t ht => (fn m' k t).mpr (all (l t) ht))
      refine ⟨l B, fun s => ⟨fun hs => ?_, fun hs => ?_⟩, decide⟩
      · let s' : Q.Domain := ⟨s.val, ht B.val B.property s.val hs⟩
        obtain ⟨hf, t, hA, hq⟩ := (pull s').mp hs
        exact ⟨(fn n' k s').mp hf, l t, hA, (cp m' n' k q' s' t).mp hq⟩
      · obtain ⟨hf, t, hA, hq⟩ := hs
        let s' : Q.Domain := ⟨s.val, finite n s hn hf⟩
        let t' : Q.Domain := ⟨t.val, ht A.val A'.property t.val hA⟩
        exact (pull s').mpr ⟨(fn n' k s').mpr hf, t', hA, (cp m' n' k q' s' t').mpr hq⟩
    · intro n a U D ha hu hd μ hμ f hf
      let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
      let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
      obtain ⟨m, _, hm, hm', _⟩ := measures.measure a' u ((entry a' u e).mpr hu)
      have eq := ((fn m z a').mp hm').domain_eq_l he' ha
      have hn : M.mem n.val ω := congrArg Subtype.val eq ▸ hm
      let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
      let D' : Q.Domain := ⟨D.val, family_owned n D hn (fun s hs => (hd s).mp hs)⟩
      let μ' : Q.Domain := ⟨μ.val, ht κ hκ μ.val hμ⟩
      let f' : Q.Domain := ⟨f.val, own μ U f μ'.property u.property hf⟩
      obtain ⟨B, hB, spec⟩ := complete n' a' u D' ((fn n' z a').mpr ha) ((entry a' u e).mpr hu)
        (fun s => (hd (l s)).trans (fn n' k s).symm) μ' hμ f' ((fn μ' u f').mpr hf)
      have read (x : Q.Domain) : M.mem x.val B.val ↔ M.mem x.val D.val ∧ Ed_all_d μ U f (l x) := by
        let η : Env Q 4 := ⟨Fin.cases x (Fin.cases f' (Fin.cases u (fun _ => μ'))), fun _ => μ'⟩
        exact (spec x).trans (and_congr Iff.rfl ((ed_all_sat_l he η (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
          ((delta _ (ed_all_delta_l ..) η).trans (ed_all_sat_l he' ..))))
      exact ⟨l B, hB, fun x => ⟨fun hxB => (read ⟨x.val, ht B.val B.property x.val hxB⟩).mp hxB,
        fun hxD => (read ⟨x.val, ht D.val D'.property x.val hxD.1⟩).mpr hxD⟩⟩
    · intro p n a U i r β γ hn ha hu hi hr
      let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
      let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
      let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
      have ib := rd_entry_transitive_l ht a'.property ((rt_entry_l hx nx hZF.1 i β a).mp hi)
      have rc := rd_entry_transitive_l ht a'.property ((rt_entry_l hx nx hZF.1 r γ a).mp hr)
      let i' : Q.Domain := ⟨i.val, ib.1⟩; let r' : Q.Domain := ⟨r.val, rc.1⟩
      let β' : Q.Domain := ⟨β.val, ib.2⟩; let γ' : Q.Domain := ⟨γ.val, rc.2⟩
      obtain ⟨B, spec, decide⟩ := atoms p n' a' u i' r' β' γ' hn ((fn n' z a').mpr ha)
        ((entry a' u e).mpr hu) ((entry i' β' a').mpr hi) ((entry r' γ' a').mpr hr)
      have read (s : Q.Domain) : M.mem s.val B.val ↔ Fn0_d n (l k) (l s) ∧ Ea_test_d p (l k) i r (l s) := by
        let η : Env Q 4 := ⟨Fin.cases s (Fin.cases r' (Fin.cases i' (fun _ => k))), fun _ => k⟩
        exact (spec s).trans (and_congr (fn n' k s) ((ea_test_sat_l he η p (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
          ((delta _ (ea_test_delta_l ..) η).trans (ea_test_sat_l he' ..))))
      refine ⟨l B, fun s => ⟨fun hs => (read ⟨s.val, ht B.val B.property s.val hs⟩).mp hs,
        fun hs => (read ⟨s.val, finite n s hn hs.1⟩).mpr hs⟩, ?_⟩
      cases p with
      | false => exact decide
      | true => exact decide.trans ⟨congrArg l, fun h => Subtype.ext (congrArg (fun x : N.Domain => x.val) h)⟩
    · intro n a U D f i β A hn ha hu hd hf hi hA reg
      let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
      let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
      let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
      let D' : Q.Domain := ⟨D.val, family_owned n D hn (fun s hs => (hd s).mp hs)⟩
      let f' : Q.Domain := ⟨f.val, own D (l k) f D'.property hκ hf⟩
      have ib := rd_entry_transitive_l ht a'.property ((rt_entry_l hx nx hZF.1 i β a).mp hi)
      let i' : Q.Domain := ⟨i.val, ib.1⟩; let β' : Q.Domain := ⟨β.val, ib.2⟩
      let A' : Q.Domain := ⟨A.val, ht U.val u.property A.val hA⟩
      obtain ⟨m, b, W, γ, B, hm, succ, fb, ab, last, lt, hbW, hBW, graph⟩ := normal n' a' u D' f' i' β' A' hn
        ((fn n' z a').mpr ha) ((entry a' u e).mpr hu) (fun s => (hd (l s)).trans (fn n' k s).symm)
        ((fn D' k f').mpr hf) ((entry i' β' a').mpr hi) hA
        (fun s hs x y hfx hiy => reg (l s) hs (l x) (l y) ((entry s x f').mp hfx) ((entry i' y s).mp hiy))
      refine ⟨l m, l b, l W, l γ, l B, hm, (rt_successor_l hx nx hZF.1 (l m) n).mpr
        ((rt_successor_l ht nv hZF.1 m n').mp succ), (fn m z b).mp fb, (sub a' b).mp ab,
        (entry n' γ b).mp last, lt, (entry b W e).mp hbW, hBW, fun s hs => ?_⟩
      let s' : Q.Domain := ⟨s.val, ht B.val B.property s.val hs⟩
      let η : Env Q 5 := ⟨Fin.cases s' (Fin.cases f' (Fin.cases A' (Fin.cases k (fun _ => n')))), fun _ => n'⟩
      exact ((en_graph_sat_l he η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((delta _ (en_graph_delta_l ..) η).trans (en_graph_sat_l he' ..))).mp (graph s' hs)
    · intro n a U hn ha hu A
      let n' : Q.Domain := ⟨n.val, ht ω hω n.val hn⟩
      let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
      let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
      have read (B : Q.Domain) := principal n' a' u hn ((fn n' k a').mpr ha) ((entry a' u e).mpr hu) B
      constructor
      · intro hA
        let B : Q.Domain := ⟨A.val, ht U.val u.property A.val hA⟩
        obtain ⟨all, haA⟩ := (read B).mp hA
        exact ⟨fun s hs => (fn n' k ⟨s.val, ht A.val B.property s.val hs⟩).mp (all _ hs), haA⟩
      · rintro ⟨all, haA⟩
        let B : Q.Domain := ⟨A.val, family_owned n A hn all⟩
        exact (read B).mpr ⟨fun s hs => (fn n' k s).mpr (all (l s) hs), haA⟩
    · intro a U i β hu hi hβ x s single hs
      let a' : Q.Domain := ⟨a.val, (endpoints a U hu).1⟩
      let u : Q.Domain := ⟨U.val, (endpoints a U hu).2⟩
      have ib := rd_entry_transitive_l ht a'.property ((rt_entry_l hx nx hZF.1 i β a).mp hi)
      let i' : Q.Domain := ⟨i.val, ib.1⟩; let β' : Q.Domain := ⟨β.val, ib.2⟩
      let s' : Q.Domain := ⟨s.val, ht U.val u.property s.val hs⟩
      let x' : Q.Domain := ⟨x.val, ht s.val s'.property x.val ((single x).mpr rfl)⟩
      exact nonprincipal a' u i' β' ((entry a' u e).mpr hu) ((entry i' β' a').mpr hi) hβ x' s'
        (fun y => (single (l y)).trans ⟨fun h => Subtype.ext (congrArg (fun x : N.Domain => x.val) h), congrArg l⟩) hs
  · -- 可数层族的整个值域由有限 κ 序列界收纳，所以无需 α 的共尾性假设。
    simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff]
    intro H f levels fiber
    have levels := (ef_levels_relative_l hZF.1 hx (source.algebra_l (ZF.modelsKP hZF)) nx ..).mp levels
    have fiber := (es_fiber_relative_l (ZF.modelsKP hZF) hx nx ..).mp fiber
    obtain ⟨c, code⟩ := source.code
    obtain ⟨B, hB, range⟩ := sc_range_source_l hZF source.omega hx code source.theory H.property
    have hBV := rank.subsets_mem_l hx hV hα hP hB (fun A hA s hs => by
      obtain ⟨n, hn⟩ := (range A).mp hA
      obtain ⟨_, fn⟩ := levels.1
      exact (seq s).mpr ⟨n, (fn.bound_l hn).1, fn0_function_l (ZF.modelsKP hZF) (levels.2 n A hn s hs)⟩)
    obtain ⟨_, fh⟩ := levels.1
    have hH := rank.relation_mem_l hx hV hα hω hBV H.property
      (fh.retarget_l (fun n A hn => (range A).mpr ⟨n, hn⟩)).1
    have hf := rank.relation_mem_l hx hV hα hω hL f.property fiber.1.1
    obtain ⟨g, hg, gf⟩ := ex_owned_fiber_l hZF ht algebra hω hκ hL hF countable hH hf levels fiber
    exact ⟨⟨g, hx V hV g hg⟩, (ef_fiber_relative_l hZF.1 hx nx ..).mpr gf⟩

end YesMetaZFC.SetTheory.LargeCardinal
