import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyExtend

/-! # 复制历史的恒等延伸

空操作沿原来的直接前驱复制同一行。新增箭头是真实恒等图；全部旧交换
方块经它复合，支撑列不增加条目。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.pad_extend_l {ω c T Q G E L n m H S Q' G' : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (inactive : ∀ ρ, ¬ Rd_entry_d n ρ L) :
    ∃ l J S' Q'' G'', M.SuccessorOf l m ∧ Ic_history_d hZF ω T Q G E L l J S' Q'' G'' ∧
      M.MemberSubset H J ∧ M.MemberSubset Q' Q'' ∧ M.MemberSubset G' G'' := by
  have hω := nice.tree.omega
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hn
  have eq := hm₀.eq hZF.1 hm
  subst m₀
  obtain ⟨k, b, a, d, j₀, p, pred, hb, ha, hd, hj₀, hp, step⟩ := nice.tree.steps n m hmω hm
  have pad : (∀ x, ¬ M.mem x p) ∧ k = n ∧ d = b ∧ ∀ x y, Rd_entry_d x y j₀ → x = y := by
    rcases step with pad | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
    · exact pad
    · exact (inactive ρ ((nice.levels n ρ).mpr ⟨p, κ, F, hp, pay⟩)).elim
  obtain ⟨empty, ek, ed, ident₀⟩ := pad
  subst k d
  obtain ⟨r, hr⟩ := (hist.domain n).mp hm.predecessor_mem
  obtain ⟨b₀, X, A, π, z, Z, α, cell, hb₀, hz, row⟩ := hist.rows n r hr
  have eq := nice.tree.diagram.model_function.2 n b₀ b hb₀ hb
  subst b₀
  have ar : Ic_at_d H n X A π z Z α := ⟨r, hr, cell⟩
  have row₀ := row
  obtain ⟨Rx, _, Rz, _, _, _, _, mx, _, mz, _, _, _, hA, _, _, emb⟩ := row
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
          exact ⟨nice.tree.diagram.order.refl m hmω, hl.predecessor_mem⟩
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
  refine ⟨l, J, S', Q'', G'', hl, ⟨diagram, order, jf.2.1, jf.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    sub hist.function.1 (fun i t ht => (entries i t).mpr (Or.inl ht)),
    sub hist.diagram.model_function.1 (fun i a ha => (qs i a).mpr (Or.inl ha)), sub hist.diagram.map_function.1 gm⟩
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
      · rcases hist.past i n X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α ai ar hin with h | ⟨k, ρ, φ, hik, hk, rest⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, ρ, φ, hik, (hm k).mpr (Or.inl hk), rest⟩
      · have eq := hZF.1.eq_of_same_members i n eq
        subst i
        obtain ⟨e₁, e₂, e₃, _, _, _⟩ := ai.unique_l (ZF.modelsKP hZF) hist.function ar
        subst X₁ A₁ π₁
        exact Or.inl ⟨rfl, rfl, rfl, inactive⟩
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
    · have hi := (nice.tree.diagram.order.forward i j (nice.tree.diagram.map_bound_l hZF hf)).elim
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
        exact nice.tree.diagram.identity m f hf x y hxy ▸ diagram.identity m g hg x' y' hyy ▸ hxx
      · have hik := (hist.order i n).mp (hist.diagram.map_bound_l hZF hg₀)
        have ai₀ := (old (hist.diagram.order.bound i n (hist.diagram.map_bound_l hZF hg₀)).1).mp ai
        obtain ⟨b₁, hb₁, _, row₁⟩ := hist.row_l hZF ai₀
        obtain ⟨R₁, _, _, _, _, _, _, mi, _, _, _, _, _, _, _, _, em⟩ := row₁
        obtain ⟨f₀, hf₀⟩ := nice.tree.diagram.map_l hZF hik.1
        have ef := nice.tree.diagram.elementary i n f₀ b₁ X₁ R₁ b X Rx hf₀ hb₁ hb mi.1 mx.1
        obtain ⟨v, hv, hxv⟩ := ef.1.1.2.2 x (em.1.1.input_mem_of_pairMember hxx)
        obtain ⟨w, _, hvw⟩ := (nice.tree.diagram.elementary n m j₀ b X Rx b X Rx hj₀ hb hd mx.1 mx.1).1.1.2.2 v hv
        have eq := (nice.tree.diagram.elementary i m f b₁ X₁ R₁ b X Rx hf hb₁ hd mi.1 mx.1).1.1.1.2 x w y
          (nice.tree.diagram.comp i n m f₀ j₀ f hf₀ hj₀ hf x v w hxv hvw) hxy
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
      exact (inactive ρ (eq ▸ (nice.levels i ρ).mpr ⟨p₁, κ, F, hp₁, pay⟩)).elim
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

theorem Ic_history_d.extend_l (hZFC : M.Models ZFC) {ω c T Q G E L n m H S Q' G' : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (hist : Ic_history_d (ZFC.models_zf_l hZFC) ω T Q G E L m H S Q' G')
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) :
    ∃ l J S' Q'' G'', M.SuccessorOf l m ∧
      Ic_history_d (ZFC.models_zf_l hZFC) ω T Q G E L l J S' Q'' G'' ∧
      M.MemberSubset H J ∧ M.MemberSubset Q' Q'' ∧ M.MemberSubset G' G'' := by
  classical
  by_cases active : ∃ ρ, Rd_entry_d n ρ L
  · exact hist.active_extend_l hZFC nice hn hm active
  · exact hist.pad_extend_l (ZFC.models_zf_l hZFC) nice hn hm (fun ρ h => active ⟨ρ, h⟩)

end YesMetaZFC.SetTheory.LargeCardinal
