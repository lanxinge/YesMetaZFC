import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax

/-! # 复制历史的恒等延伸

空操作沿原来的直接前驱复制同一行。新增箭头是真实恒等图；全部旧交换
方块经它复合，支撑列不增加条目。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.pad_extend_l {ω c θ T Q G E L n m H S Q' G' : M.Domain}
    (tree : It_tree_d hZF ω c θ T Q G E)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hm : M.SuccessorOf m n) (hmθ : M.mem m θ) (inactive : ∀ ρ, ¬ Rd_entry_d n ρ L) :
    ∃ l J S' Q'' G'', M.SuccessorOf l m ∧ Ic_history_d hZF ω T Q G E L l J S' Q'' G'' ∧
      M.MemberSubset H J ∧ M.MemberSubset Q' Q'' ∧ M.MemberSubset G' G'' ∧
      ∀ N R B σ u U β χ, Ic_at_d H n N B σ u U β → Ic_bound_d I H Q N R σ n χ →
        Ic_at_d J m N B σ u U β ∧ Ic_bound_d I J Q N R σ m χ := by
  have hω := tree.omega
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨k, b, a, d, j₀, p, pred, hb, ha, hd, hj₀, hp, step⟩ := tree.steps n m hmθ hm
  have pad : (∀ x, ¬ M.mem x p) ∧ k = n ∧ d = b ∧ ∀ x y, Rd_entry_d x y j₀ → x = y := by
    rcases step with pad | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
    · exact pad
    · exact (inactive ρ ((levels n ρ).mpr ⟨p, κ, F, hp, pay⟩)).elim
  obtain ⟨empty, ek, ed, ident₀⟩ := pad
  subst k d
  obtain ⟨r, hr⟩ := (hist.domain n).mp hm.predecessor_mem
  obtain ⟨b₀, X, A, π, z, Z, α, cell, hb₀, hz, row⟩ := hist.rows n r hr
  have eq := tree.diagram.model_function.2 n b₀ b hb₀ hb
  subst b₀
  have ar : Ic_at_d H n X A π z Z α := ⟨r, hr, cell⟩
  have row₀ := row
  obtain ⟨Rx, _, Rz, _, _, _, mx, ma, mz, _, _, hA, _, _, emb⟩ := row
  obtain ⟨j, jj, js⟩ := smap_identity_l I hZF (c := z) (X := Z) hω
  obtain ⟨l, S', Q'', G'', e, hl, diagram, ss, qs, gs, edge⟩ :=
    it_diagram_extend_l hZF hω hist.diagram hm hz mz.1 mz.1 jj
  obtain ⟨J, jf, entries⟩ := Structure.IsSequenceOfLength.exists_append (value := r) (ZF.modelsKP hZF) I
    ⟨hist.diagram.order.ordinal, hist.function, hist.domain⟩ diagram.order.ordinal hl
  have top : Ic_at_d J m X A π z Z α := ⟨r, (entries m r).mpr (Or.inr ⟨rfl, rfl⟩), cell⟩
  have old_entry {i} (hi : M.mem i m) (t) : Rd_entry_d i t J ↔ Rd_entry_d i t H :=
    (entries i t).trans ⟨fun h => h.elim id (fun h => (ir m (h.1 ▸ hi)).elim), Or.inl⟩
  have old {i Y B σ u U β} (hi : M.mem i m) : Ic_at_d J i Y B σ u U β ↔ Ic_at_d H i Y B σ u U β :=
    exists_congr fun t => and_congr (old_entry hi t) Iff.rfl
  have split i : M.mem i l ↔ M.mem i m ∨ i = m := (hl i).trans
    (or_congr Iff.rfl ⟨hZF.1.eq_of_same_members i m, fun eq => eq ▸ fun _ => Iff.rfl⟩)
  have bound {i Y B σ u U β} (hi : Ic_at_d J i Y B σ u U β) : M.mem i l :=
    (jf.2.2 i).mpr (hi.imp fun _ h => h.1)
  have gold {i j f} (hj : M.mem j m) (hf : It_map_d G'' i j f) : It_map_d G' i j f :=
    ((gs i j f).mp hf).elim id (fun h => (ir m (h.1 ▸ hj)).elim)
  have order i j : Rd_entry_d i j S' ↔ Rd_entry_d i j T ∧ M.mem j l := by
    rw [ss, hist.order]
    constructor
    · rintro (⟨hij, hj⟩ | ⟨eq, h⟩)
      · exact ⟨hij, (split j).mpr (Or.inl hj)⟩
      · subst j
        rcases h with eq | hik
        · subst i
          exact ⟨tree.diagram.order.refl m hmθ, hl.predecessor_mem⟩
        · exact ⟨(pred.2 i).mpr (Or.inr ((hist.order i n).mp hik).1), hl.predecessor_mem⟩
    · rintro ⟨hij, hj⟩
      rcases (split j).mp hj with hj | eq
      · exact Or.inl ⟨hij, hj⟩
      · subst j
        exact Or.inr ⟨rfl, ((pred.2 i).mp hij).imp id (fun h => (hist.order i n).mpr ⟨h, hm.predecessor_mem⟩)⟩
  have sub {A B : M.Domain} (rel : M.IsSetRelation I A)
      (keep : ∀ x y, Rd_entry_d x y A → Rd_entry_d x y B) : M.MemberSubset A B := by
    intro p hp
    obtain ⟨x, y, pair⟩ := rel p hp
    obtain ⟨q, qp, hq⟩ := keep x y ⟨p, pair, hp⟩
    exact kpair_unique_l M hZF.1 qp pair ▸ hq
  have gm r f (hr : Rd_entry_d r f G') : Rd_entry_d r f G'' := by
    obtain ⟨i, j, pair⟩ := hist.diagram.order.relation r ((hist.diagram.map_domain r).mpr ⟨f, hr⟩)
    obtain ⟨q, qp, hq⟩ := (gs i j f).mpr (Or.inl ⟨r, pair, hr⟩)
    exact kpair_unique_l M hZF.1 qp pair ▸ hq
  have result : Ic_history_d hZF ω T Q G E L l J S' Q'' G'' := by
    refine ⟨diagram, order, jf.2.1, jf.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i t ht
      rcases (entries i t).mp ht with ht | ⟨ei, et⟩
      · obtain ⟨b, Y, B, σ, u, U, β, cell, hb, hu, row⟩ := hist.rows i t ht
        exact ⟨b, Y, B, σ, u, U, β, cell, hb, (qs i u).mpr (Or.inl hu), row⟩
      · subst i t
        exact ⟨b, X, A, π, z, Z, α, cell, hd, (qs m z).mpr (Or.inr ⟨rfl, rfl⟩), row₀⟩
    · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ai aj hij
      rcases (split j).mp (bound aj) with hj | eq
      · exact hist.past i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂
          ((old (hist.diagram.order.ordinal.transitive j hj i hij)).mp ai) ((old hj).mp aj) hij
      · subst j
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
        subst X₂ A₂ π₂ z₂ Z₂ α₂
        have ai := (old hij).mp ai
        rcases (hm i).mp hij with hin | eq
        · rcases hist.past i n X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α ai ar hin with
            ⟨c₀, hci, hcn, rest⟩ | ⟨k, ρ, l, φ, U₀, V₀, D₀, t₀, c₀, d₀, R₀, S₀, hik, hk, hρ, first, hci, hdn, mc, md, same⟩
          · have eq := tree.diagram.model_function.2 n c₀ b hcn hb
            subst c₀
            exact Or.inl ⟨b, hci, hd, rest⟩
          · have eq := tree.diagram.model_function.2 n d₀ b hdn hb
            subst d₀
            exact Or.inr ⟨k, ρ, l, φ, U₀, V₀, D₀, t₀, c₀, b, R₀, S₀,
              hik, (hm k).mpr (Or.inl hk), hρ, first, hci, hd, mc, md, same⟩
        · have eq := hZF.1.eq_of_same_members i n eq
          subst i
          obtain ⟨e₁, e₂, e₃, _, _, _⟩ := ai.unique_l (ZF.modelsKP hZF) hist.function ar
          subst X₁ A₁ π₁
          exact Or.inl ⟨b, hb, hd, rfl, rfl, rfl, inactive⟩
    · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ai aj hg
      rcases (split j).mp (bound aj) with hj | eq
      · have hi := (diagram.order.forward i j (diagram.map_bound_l hZF hg)).elim
          (fun eq => eq.symm ▸ hj) (fun hi => hist.diagram.order.ordinal.transitive j hj i hi)
        exact hist.cuts i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ((old hi).mp ai) ((old hj).mp aj) (gold hj hg)
      · subst j
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
        subst X₂ A₂ π₂ z₂ Z₂ α₂
        rcases (gs i m g).mp hg with hg₀ | ⟨_, ⟨ei, _⟩ | ⟨g₀, hg₀, comp⟩⟩
        · exact (ir m (hist.diagram.order.bound i m (hist.diagram.map_bound_l hZF hg₀)).2).elim
        · subst i
          rw [(ai.unique_l (ZF.modelsKP hZF) jf.2.1 top).2.1]
          obtain ⟨B, _, hAB⟩ := (diagram.elementary m m g z Z Rz z Z Rz hg
            ((qs m z).mpr (Or.inr ⟨rfl, rfl⟩)) ((qs m z).mpr (Or.inr ⟨rfl, rfl⟩)) mz.1 mz.1).1.1.2.2 A hA
          exact (diagram.identity m g hg A B hAB).symm ▸ hAB
        · exact (comp.2 A₁ A).mpr ⟨A, hist.cuts i n X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α g₀
            ((old (hist.diagram.order.bound i n (hist.diagram.map_bound_l hZF hg₀)).1).mp ai) ar hg₀, (js A A).mpr ⟨hA, rfl⟩⟩
    · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ f g ai aj hf hg x x' y y' hxx hxy hyy
      rcases (split j).mp (bound aj) with hj | eq
      · have hi := (tree.diagram.order.forward i j (tree.diagram.map_bound_l hZF hf)).elim
          (fun eq => eq.symm ▸ hj) (fun hi => hist.diagram.order.ordinal.transitive j hj i hi)
        exact hist.squares i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ f g
          ((old hi).mp ai) ((old hj).mp aj) hf (gold hj hg) x x' y y' hxx hxy hyy
      · subst j
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
        subst X₂ A₂ π₂ z₂ Z₂ α₂
        rcases (gs i m g).mp hg with hg₀ | ⟨_, ⟨ei, _⟩ | ⟨g₀, hg₀, comp⟩⟩
        · exact (ir m (hist.diagram.order.bound i m (hist.diagram.map_bound_l hZF hg₀)).2).elim
        · subst i
          obtain ⟨e₁, e₂, e₃, _, _, _⟩ := ai.unique_l (ZF.modelsKP hZF) jf.2.1 top
          subst X₁ A₁ π₁
          exact tree.diagram.identity m f hf x y hxy ▸ diagram.identity m g hg x' y' hyy ▸ hxx
        · have hik := (hist.order i n).mp (hist.diagram.map_bound_l hZF hg₀)
          have ai₀ := (old (hist.diagram.order.bound i n (hist.diagram.map_bound_l hZF hg₀)).1).mp ai
          obtain ⟨b₁, hb₁, _, row₁⟩ := hist.row_l hZF ai₀
          obtain ⟨R₁, _, _, _, _, _, mi, _, _, _, _, _, _, _, em⟩ := row₁
          obtain ⟨f₀, hf₀⟩ := tree.diagram.map_l hZF hik.1
          have ef := tree.diagram.elementary i n f₀ b₁ X₁ R₁ b X Rx hf₀ hb₁ hb mi mx
          obtain ⟨v, hv, hxv⟩ := ef.1.1.2.2 x (em.1.1.input_mem_of_pairMember hxx)
          obtain ⟨w, _, hvw⟩ := (tree.diagram.elementary n m j₀ b X Rx b X Rx hj₀ hb hd mx mx).1.1.2.2 v hv
          have eq := (tree.diagram.elementary i m f b₁ X₁ R₁ b X Rx hf hb₁ hd mi mx).1.1.1.2 x w y
            (tree.diagram.comp i n m f₀ j₀ f hf₀ hj₀ hf x v w hxv hvw) hxy
          obtain ⟨v', hxv', hv'y⟩ := (comp.2 x' y').mp hyy
          have ev : v = y := (ident₀ v w hvw).trans eq
          have ev' := ((js v' y').mp hv'y).2
          exact ev ▸ ev' ▸ hist.squares i n X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α f₀ g₀ ai₀ ar hf₀ hg₀ x x' v v' hxx hxv hxv'
    · intro i j k N B σ u U β X₁ A₁ π₁ z₁ Z₁ α₁ P C τ v V γ p₁ κ ρ F f succ pred' ai ak aj hp₁ pay hf
      rcases (split j).mp (bound aj) with hj | eq
      · exact hist.steps i j k N B σ u U β X₁ A₁ π₁ z₁ Z₁ α₁ P C τ v V γ p₁ κ ρ F f succ pred'
          ((old (hist.diagram.order.ordinal.transitive j hj i succ.predecessor_mem)).mp ai)
          ((old (hist.diagram.order.ordinal.transitive j hj k pred'.1)).mp ak) ((old hj).mp aj) hp₁ pay (gold hj hf)
      · subst j
        have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
        exact (inactive ρ (eq ▸ (levels i ρ).mpr ⟨p₁, κ, F, hp₁, pay⟩)).elim
    · intro i j p₁ succ hjl hp₁ empty₁
      rcases (split j).mp hjl with hj | eq
      · have hi := hist.diagram.order.ordinal.transitive j hj i succ.predecessor_mem
        obtain ⟨same, ident⟩ := hist.pads i j p₁ succ hj hp₁ empty₁
        exact ⟨fun r => (old_entry hi r).trans ((same r).trans (old_entry hj r).symm),
          fun f x y hf => ident f x y (gold hj hf)⟩
      · subst j
        have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
        subst i
        refine ⟨fun t => (old_entry hm.predecessor_mem t).trans ?_, ?_⟩
        · have ht : Rd_entry_d m t J ↔ t = r := (entries m t).trans
            ⟨fun h => h.elim (fun h => (ir m ((hist.domain m).mpr ⟨t, h⟩)).elim) And.right,
              fun eq => Or.inr ⟨rfl, eq⟩⟩
          exact (show Rd_entry_d n t H ↔ t = r from ⟨fun h => hist.function.2 n t r h hr, fun eq => eq.symm ▸ hr⟩).trans ht.symm
        · intro f x y hf hxy
          exact ((js x y).mp (diagram.map_unique_l hZF hf edge ▸ hxy)).2

    · intro i j r X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ρ ψ a b ai aj succ hr hρ hψ ha hb hij
      rcases (split r).mp hr with hr | eq
      · have hj := hist.diagram.order.ordinal.transitive r hr j succ.predecessor_mem
        have hi := hist.diagram.order.ordinal.transitive j hj i hij
        exact hist.increasing i j r X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ρ ψ a b
          ((old hi).mp ai) ((old hj).mp aj) succ hr hρ hψ ha hb hij
      · subst r
        have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
        exact (inactive ψ (eq ▸ hψ)).elim
  have last {N B σ u U β} : Ic_at_d J m N B σ u U β ↔ Ic_at_d H n N B σ u U β := by
    constructor
    · intro aj
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
      subst N B σ u U β
      exact ar
    · intro ai
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ai.unique_l (ZF.modelsKP hZF) hist.function ar
      subst N B σ u U β
      exact top
  have code d : Rd_entry_d m d Q ↔ Rd_entry_d n d Q :=
    ⟨fun h => (tree.diagram.model_function.2 m d b h hd).symm ▸ hb,
      fun h => (tree.diagram.model_function.2 n d b h hb).symm ▸ hd⟩
  have height_eq {N R σ} i a (hi : M.mem i n) :
      Ic_height_d I J Q N R σ m i a ↔ Ic_height_d I H Q N R σ n i a := by
    refine and_congr_right fun _ => ?_
    refine exists_congr fun X => exists_congr fun A => exists_congr fun π =>
      exists_congr fun z => exists_congr fun Z => exists_congr fun α =>
      exists_congr fun B => exists_congr fun u => exists_congr fun U => exists_congr fun β =>
      exists_congr fun c => exists_congr fun d => exists_congr fun R => exists_congr fun L =>
      exists_congr fun φ => exists_congr fun V => exists_congr fun W => exists_congr fun D => exists_congr fun t => ?_
    exact and_congr (old ((hm i).mpr (Or.inl hi)))
      (and_congr last (and_congr Iff.rfl (and_congr (code d) Iff.rfl)))
  -- 新增行与原末行完全相同，不能产生一个带全局缺失子集的共同端点。
  have no_new {R a} (ha : Ic_height_d I J Q X R π m n a) : False := by
    obtain ⟨_, X₁, A₁, π₁, z₁, Z₁, α₁, B, u, U, β, c₁, d₁, R₁, ρ, φ, V, W, D, t,
      ai, aj, qi, qj, mi, mj, common⟩ := ha
    obtain ⟨e₁, e₂, e₃, _, _, _⟩ := ((old hm.predecessor_mem).mp ai).unique_l (ZF.modelsKP hZF) hist.function ar
    subst X₁ A₁ π₁
    have eq := (aj.unique_l (ZF.modelsKP hZF) jf.2.1 top).2.1
    subst B
    have eq := tree.diagram.model_function.2 n c₁ b qi hb
    subst c₁
    have eq := tree.diagram.model_function.2 m d₁ b qj hd
    subst d₁
    have eq := (smdl_unique_l I mi mx).2
    subst R₁
    have eq := (smdl_unique_l I mj mx).2
    subst R
    exact common.not_refl_l hZF hω mx ma emb
  refine ⟨l, J, S', Q'', G'', hl, result,
    sub hist.function.1 (fun i t ht => (entries i t).mpr (Or.inl ht)),
    sub hist.diagram.model_function.1 (fun i a ha => (qs i a).mpr (Or.inl ha)), sub hist.diagram.map_function.1 gm, ?_⟩
  intro N R B σ u U β χ an bound
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := an.unique_l (ZF.modelsKP hZF) hist.function ar
  subst N B σ u U β
  refine ⟨top, bound.ordinal, ?_, ?_⟩
  · rcases bound.origin with empty | ⟨i, hi, height⟩
    · exact Or.inl empty
    · exact Or.inr ⟨i, (hm i).mpr (Or.inl hi), (height_eq i χ hi).mpr height⟩
  · intro i a hi ha
    rcases (hm i).mp hi with hi | eq
    · exact bound.upper i a hi ((height_eq i a hi).mp ha)
    · have eq := hZF.1.eq_of_same_members i n eq
      subst i
      exact (no_new ha).elim

end YesMetaZFC.SetTheory.LargeCardinal
