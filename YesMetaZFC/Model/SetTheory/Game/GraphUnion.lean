import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.CountableChain

/-! # 内部递增有限图列的 ω 取并

长度每次恰增一，内部归纳给出指标不超过长度，因此并图的定义域是整个 ω。
两条图条目在共同阶段比较；每个原有限图恰是并图在自身长度上的限制。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_graph_union_l {ω N L G : M.Domain} (hw : M.IsOmega ω) (nt : M.TransitiveSet N)
    (length : Fn0_d ω ω L) (graphs : Fn0_d ω N G)
    (finite : ∀ i n g, Rd_entry_d i n L → Rd_entry_d i g G → Tg_graph_d I n g)
    (step : ∀ i j n m, M.SuccessorOf j i → Rd_entry_d i n L → Rd_entry_d j m L → M.SuccessorOf m n)
    (grow : ∀ i j g h, M.SuccessorOf j i → Rd_entry_d i g G → Rd_entry_d j h G → M.MemberSubset g h) :
    ∃ f, Fn0_d ω N f ∧ Cc_union_d I G f ∧
      ∀ i n g, Rd_entry_d i n L → Rd_entry_d i g G → M.IsRestrictionOf I g f n := by
  have lf := fn0_function_l (ZF.modelsKP hZF) length
  have gf := fn0_function_l (ZF.modelsKP hZF) graphs
  have ord := hw.isOrdinal (ZF.modelsKP hZF)
  have inc := ZF.cc_increasing_of_successor_l I hZF hw gf grow
  let ρ : Env M 1 := ⟨fun _ => L, fun _ => L⟩
  let φ : UnarySchema 1 := { body := .forallE (.imp (rd_entry0_m (.bound 1) .newest (.bound 2))
    (Formula.subset (.bound 1) .newest)) }
  have sat i : φ.denote ρ i ↔ ∀ n, Rd_entry_d i n L → M.MemberSubset i n := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff]; rfl
  have lower i (hi : M.mem i ω) : ∀ n, Rd_entry_d i n L → M.MemberSubset i n := by
    apply hw.induction (fun i => ∀ n, Rd_entry_d i n L → M.MemberSubset i n) ?_ ?_ ?_ i hi
    · obtain ⟨C, cs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun i => (cs i).trans (and_congr_right fun _ => sat i)⟩
    · exact fun e empty _ _ x hx => (empty x hx).elim
    · intro i hi ih j succ m hm
      obtain ⟨n, hn, hiL⟩ := length.2.1 i hi
      have next := step i j n m succ hiL hm
      have below : i = n ∨ M.mem i n := by
        rcases ord.wellOrder.linear.compare i hi n hn with eq | lt | gt
        · exact Or.inl (hZF.1.eq_of_same_members i n eq)
        · exact Or.inr lt
        · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (ih n hiL n gt)).elim
      intro x hx
      rcases (succ x).mp hx with lt | eq
      · exact (next x).mpr (Or.inl (ih n hiL x lt))
      · have eq := hZF.1.eq_of_same_members x i eq
        subst x
        exact below.elim (fun eq => eq.symm ▸ next.predecessor_mem) (fun lt => (next i).mpr (Or.inl lt))
  obtain ⟨R, rs⟩ := ZF.exists_range_of_setFunction hZF I gf.1 gf.2.1
  obtain ⟨f, fs⟩ := KP.exists_union (ZF.modelsKP hZF) R
  have union : Cc_union_d I G f := fun p => (fs p).trans ⟨fun ⟨g, hg, hp⟩ => by
    obtain ⟨i, hi⟩ := (rs g).mp hg
    exact ⟨i, g, hi, hp⟩, fun ⟨i, g, hi, hp⟩ => ⟨g, (rs g).mpr ⟨i, hi⟩, hp⟩⟩
  have graph i g (hg : Rd_entry_d i g G) : ∃ n, M.mem n ω ∧ Tg_graph_d I n g := by
    obtain ⟨n, hn, hi⟩ := length.2.1 i (graphs.bound_l hg).1
    exact ⟨n, hn, finite i n g hi hg⟩
  have push {i g x y} (hg : Rd_entry_d i g G) (hxy : Rd_entry_d x y g) : Rd_entry_d x y f := by
    obtain ⟨p, pair, hp⟩ := hxy
    exact ⟨p, pair, (union p).mpr ⟨i, g, hg, hp⟩⟩
  have pull {x y} (hxy : Rd_entry_d x y f) : ∃ i g, Rd_entry_d i g G ∧ Rd_entry_d x y g := by
    obtain ⟨p, pair, hp⟩ := hxy
    obtain ⟨i, g, hg, hp⟩ := (union p).mp hp
    exact ⟨i, g, hg, p, pair, hp⟩
  have function : M.IsSetFunction I f := by
    refine ⟨fun p hp => ?_, fun x y z hy hz => ?_⟩
    · obtain ⟨i, g, hg, hp⟩ := (union p).mp hp
      obtain ⟨_, _, fn⟩ := graph i g hg
      exact fn.1.1 p hp
    · obtain ⟨i, g, hg, hy⟩ := pull hy
      obtain ⟨j, h, hh, hz⟩ := pull hz
      obtain ⟨_, _, gp⟩ := graph i g hg
      obtain ⟨_, _, hp⟩ := graph j h hh
      have keeps {g h x y} (sub : M.MemberSubset g h) (hx : Rd_entry_d x y g) : Rd_entry_d x y h := by
        obtain ⟨p, pair, mem⟩ := hx; exact ⟨p, pair, sub p mem⟩
      rcases ord.wellOrder.linear.compare i (graphs.bound_l hg).1 j (graphs.bound_l hh).1 with eq | lt | gt
      · have eq := hZF.1.eq_of_same_members i j eq
        subst j
        have eq := gf.1.2 i h g hh hg
        exact gp.1.2 x y z hy (eq ▸ hz)
      · exact hp.1.2 x y z (keeps (inc i j g h lt hg hh) hy) hz
      · exact gp.1.2 x y z hy (keeps (inc j i h g gt hh hg) hz)
  have total i (hi : M.mem i ω) : ∃ x, M.mem x N ∧ Rd_entry_d i x f := by
    obtain ⟨j, succ, hj⟩ := hw.1.2 i hi
    obtain ⟨n, _, hn⟩ := length.2.1 j hj
    obtain ⟨g, hgN, hg⟩ := graphs.2.1 j hj
    obtain ⟨x, hx⟩ := ((finite j n g hn hg).2 i).mp (lower j hj n hn i succ.predecessor_mem)
    exact ⟨x, (rd_entry_transitive_l nt hgN hx).2, push hg hx⟩
  have domain : M.IsDomainOf I ω f := fun i => ⟨fun hi => (total i hi).imp fun _ h => h.2, fun ⟨x, hx⟩ => by
    obtain ⟨j, g, hg, hx⟩ := pull hx
    obtain ⟨n, hn, fn⟩ := graph j g hg
    exact hw.transitive (ZF.modelsKP hZF) n hn i ((fn.2 i).mpr ⟨x, hx⟩)⟩
  refine ⟨f, fn0_of_function_l (ZF.modelsKP hZF) ⟨function, domain, total⟩, union, ?_⟩
  intro i n g hn hg
  have fg := finite i n g hn hg
  refine ⟨fg.1.1, fun x y => ⟨fun h => ⟨(fg.2 x).mpr ⟨y, h⟩, push hg h⟩, fun ⟨hx, hy⟩ => ?_⟩⟩
  obtain ⟨z, hz⟩ := (fg.2 x).mp hx
  exact function.2 x z y (push hg hz) hy ▸ hz

end YesMetaZFC.SetTheory.Internal
