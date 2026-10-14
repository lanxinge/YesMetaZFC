import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyHistory
import YesMetaZFC.SetTheory.LargeCardinal.IterationNice

/-! # 原 nice 树的有限复制历史总可延伸

新行来自完整模型上的实际超幂。旧方块沿最后一条边复合；每个较早的
共同秩段及缺失子集由严格增加的支撑保持。整段历史无需固定的高度界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.active_extend_l {ω c T Q G E L n m H S Q' G' : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (active : ∃ ρ, Rd_entry_d n ρ L) :
    ∃ l J S' Q'' G'', M.SuccessorOf l m ∧ Ic_history_d hZF ω T Q G E L l J S' Q'' G'' ∧
      M.MemberSubset H J ∧ M.MemberSubset Q' Q'' ∧ M.MemberSubset G' G'' := by
  have hω := nice.tree.omega
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hn
  have eq := hm₀.eq hZF.1 hm
  subst m₀
  obtain ⟨k, b, a, d, j₀, p, κ, ρ, F, N₀, R₀, X₀, R₁, pred, hb, ha, hd, hj₀, he, payload, mn, mx,
    loc, agree, ultra, strength, card, hρ⟩ := nice.step_l hZF hmω hm active
  obtain ⟨r, hr⟩ := (hist.domain n).mp hm.predecessor_mem
  obtain ⟨b₀, N, B, σ, u, U, β, cr, hb₀, hu, own⟩ := hist.rows n r hr
  have eq := nice.tree.diagram.model_function.2 n b₀ b hb₀ hb
  subst b₀
  obtain ⟨s, hs⟩ := (hist.domain k).mp pred.1
  obtain ⟨a₀, X, A, π, z, Z, α, cs, ha₀, hz, row⟩ := hist.rows k s hs
  have eq := nice.tree.diagram.model_function.2 k a₀ a ha₀ ha
  subst a₀
  have own₀ := own
  have row₀ := row
  obtain ⟨Rn, Sn, Vn, bn, _, _, _, mn₀, mb, mu, on, _, _, _, _, _, hσ⟩ := own₀
  obtain ⟨Rx, Sx, Vx, bx, _, _, _, mx₀, ma, mz, ox, _, _, _, _, _, _⟩ := row₀
  obtain ⟨eqN, eqRn⟩ := smdl_unique_l I mn.1 mn₀.1
  subst N₀ R₀
  obtain ⟨eqX, eqRx⟩ := smdl_unique_l I mx.1 mx₀.1
  subst X₀ R₁
  have ar : Ic_at_d H n N B σ u U β := ⟨r, hr, cr⟩
  have as : Ic_at_d H k X A π z Z α := ⟨s, hs, cs⟩
  have prior : (X = N ∧ A = B ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d X A π N B σ ρ φ ∧ Es_strength_d X ρ N := by
    rcases (hm k).mp pred.1 with hk | eq
    · exact (hist.past k n X A π z Z α N B σ u U β as ar hk).prior_l
    · have eq := hZF.1.eq_of_same_members k n eq
      subst k
      have eq := as.unique_l (ZF.modelsKP hZF) hist.function ar
      exact Or.inl ⟨eq.1, eq.2.1, eq.2.2.1⟩
  obtain ⟨P, Rp, Kp, mp, sp⟩ := nice.tree.sources m d hd
  obtain ⟨κ', ρ', F', Y, v, C, γ, j, τ, next, hκσ, hρσ, hFσ, _, hAC, big, commute, exactness, adjacent, compatible, _⟩ :=
    row.step_l hZFC own mp sp loc (fun t D B ht hd hb => (agree t D B ht hd hb).symm) strength card prior ultra
  have next₀ := next
  obtain ⟨_, Sc, Vy, bc, _, _, _, _, mc, my, _, _, _, hC, _, _, hτ⟩ := next₀
  obtain ⟨l, S', Q'', G'', e, hl, diagram, ss, qs, gs, hj⟩ := it_diagram_extend_l hZF hω hist.diagram hm hz mz.1 my.1
    (big.elementary_l hZF mz.1 my.1)
  obtain ⟨t, ct⟩ := ic_cell_exists_l (ZF.modelsKP hZF) P C τ v Y γ
  obtain ⟨J, jf, js⟩ := Structure.IsSequenceOfLength.exists_append (value := t) (ZF.modelsKP hZF) I
    ⟨hist.diagram.order.ordinal, hist.function, hist.domain⟩ diagram.order.ordinal hl
  have jm i x : Rd_entry_d i x H → Rd_entry_d i x J := fun h => (js i x).mpr (Or.inl h)
  have top : Ic_at_d J m P C τ v Y γ := ⟨t, (js m t).mpr (Or.inr ⟨rfl, rfl⟩), ct⟩
  have old {i X A π z Z α} (hi : M.mem i m) : Ic_at_d J i X A π z Z α ↔ Ic_at_d H i X A π z Z α := by
    refine ⟨fun ⟨r, hr, cr⟩ => ⟨r, ?_, cr⟩, fun ⟨r, hr, cr⟩ => ⟨r, jm i r hr, cr⟩⟩
    exact ((js i r).mp hr).elim id (fun h => (ir m (h.1 ▸ hi)).elim)
  have bound {i X A π z Z α} (hi : Ic_at_d J i X A π z Z α) : M.mem i l :=
    (jf.2.2 i).mpr (hi.imp fun _ h => h.1)
  have split i : M.mem i l ↔ M.mem i m ∨ i = m := (hl i).trans
    (or_congr Iff.rfl ⟨hZF.1.eq_of_same_members i m, fun e => e ▸ fun _ => Iff.rfl⟩)
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
        · exact ⟨(pred.2 i).mpr (Or.inr ((hist.order i k).mp hik).1), hl.predecessor_mem⟩
    · rintro ⟨hij, hj⟩
      rcases (split j).mp hj with hj | eq
      · exact Or.inl ⟨hij, hj⟩
      · subst j
        exact Or.inr ⟨rfl, ((pred.2 i).mp hij).imp id (fun h => (hist.order i k).mpr ⟨h, pred.1⟩)⟩
  have rows i r (hr : Rd_entry_d i r J) : ∃ c X A π z Z α, Ic_cell_d r X A π z Z α ∧
      Rd_entry_d i c Q ∧ Rd_entry_d i z Q'' ∧ Ic_row_d hZF ω c X A π z Z α := by
    rcases (js i r).mp hr with hr | ⟨ei, er⟩
    · obtain ⟨c, X, A, π, z, Z, α, cell, hc, hz, row⟩ := hist.rows i r hr
      exact ⟨c, X, A, π, z, Z, α, cell, hc, (qs i z).mpr (Or.inl hz), row⟩
    · subst i r
      exact ⟨d, P, C, τ, v, Y, γ, ct, hd, (qs m v).mpr (Or.inr ⟨rfl, rfl⟩), next⟩
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
  refine ⟨l, J, S', Q'', G'', hl, ⟨diagram, order, jf.2.1, jf.2.2, rows, ?_, ?_, ?_, ?_, ?_⟩,
    sub hist.function.1 jm, sub hist.diagram.model_function.1 (fun i a ha => (qs i a).mpr (Or.inl ha)),
    sub hist.diagram.map_function.1 gm⟩
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ai aj hij
    rcases (split j).mp (bound aj) with hj | eq
    · exact hist.past i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂
        ((old (hist.diagram.order.ordinal.transitive j hj i hij)).mp ai) ((old hj).mp aj) hij
    · subst j
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
      subst X₂ A₂ π₂ z₂ Z₂ α₂
      have ai := (old hij).mp ai
      rcases (hm i).mp hij with hi | eq
      · rcases hist.past i n X₁ A₁ π₁ z₁ Z₁ α₁ N B σ u U β ai ar hi with
          ⟨rfl, rfl, rfl, no⟩ | ⟨k, μ, ν, hik, hk, hμ, first, same, missing⟩
        · exact Or.inr ⟨n, ρ, ρ', Or.inr hi, hm.predecessor_mem, hρ,
            fun ν hν => (no ν hν).elim, adjacent, exactness⟩
        have lt := nice.increasing k n μ ρ hμ hρ hk
        have lt' := ((mb.2 ν ρ').mp ((hσ.relation_l I hZF hω mn₀.1 mb.1 same.right_end hρσ).mp
          ((mn₀.2 μ ρ).mpr ⟨hσ.1.1.input_mem_of_pairMember same.right_end, hσ.1.1.input_mem_of_pairMember hρσ, lt⟩))).2.2
        exact Or.inr ⟨k, μ, ν, hik, (hm k).mpr (Or.inl hk), hμ, first,
          same.trans_l hZF adjacent lt lt', adjacent.strength_l hZF lt missing⟩
      · have eq := hZF.1.eq_of_same_members i n eq
        subst i
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ai.unique_l (ZF.modelsKP hZF) hist.function ar
        subst X₁ A₁ π₁ z₁ Z₁ α₁
        exact Or.inr ⟨n, ρ, ρ', Or.inl rfl, hm.predecessor_mem, hρ, fun _ _ => rfl, adjacent, exactness⟩
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ai aj hg
    rcases (split j).mp (bound aj) with hj' | eq
    · have hi : M.mem i m := (diagram.order.forward i j (diagram.map_bound_l hZF hg)).elim
        (fun eq => eq.symm ▸ hj') (fun hi => hist.diagram.order.ordinal.transitive j hj' i hi)
      exact hist.cuts i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ((old hi).mp ai) ((old hj').mp aj) (gold hj' hg)
    · subst j
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
      subst X₂ A₂ π₂ z₂ Z₂ α₂
      rcases (gs i m g).mp hg with hg₀ | ⟨_, ⟨ei, _⟩ | ⟨g₀, hg₀, comp⟩⟩
      · exact (ir m (hist.diagram.order.bound i m (hist.diagram.map_bound_l hZF hg₀)).2).elim
      · subst i
        rw [(ai.unique_l (ZF.modelsKP hZF) jf.2.1 top).2.1]
        have hv := (qs m v).mpr (Or.inr ⟨rfl, rfl⟩)
        obtain ⟨B, _, hCB⟩ := (diagram.elementary m m g v Y Vy v Y Vy hg hv hv my.1 my.1).1.1.2.2 C hC
        exact (diagram.identity m g hg C B hCB).symm ▸ hCB
      · exact (comp.2 A₁ C).mpr ⟨A, hist.cuts i k X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α g₀
          ((old (hist.diagram.order.bound i k (hist.diagram.map_bound_l hZF hg₀)).1).mp ai) as hg₀, hAC⟩
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ f g ai aj hf hg x x' y y' hxx hxy hyy
    rcases (split j).mp (bound aj) with hj' | eq
    · have hi : M.mem i m := (nice.tree.diagram.order.forward i j (nice.tree.diagram.map_bound_l hZF hf)).elim
        (fun eq => eq.symm ▸ hj') (fun hi => hist.diagram.order.ordinal.transitive j hj' i hi)
      exact hist.squares i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ f g
        ((old hi).mp ai) ((old hj').mp aj) hf (gold hj' hg) x x' y y' hxx hxy hyy
    · subst j
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
      subst X₂ A₂ π₂ z₂ Z₂ α₂
      rcases (gs i m g).mp hg with hg₀ | ⟨_, ⟨ei, _⟩ | ⟨g₀, hg₀, comp⟩⟩
      · exact (ir m (hist.diagram.order.bound i m (hist.diagram.map_bound_l hZF hg₀)).2).elim
      · subst i
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ai.unique_l (ZF.modelsKP hZF) jf.2.1 top
        subst X₁ A₁ π₁ z₁ Z₁ α₁
        exact nice.tree.diagram.identity m f hf x y hxy ▸ diagram.identity m g hg x' y' hyy ▸ hxx
      · have hik := (hist.order i k).mp (hist.diagram.map_bound_l hZF hg₀)
        have ai₀ := (old (hist.diagram.order.bound i k (hist.diagram.map_bound_l hZF hg₀)).1).mp ai
        obtain ⟨b₁, hb₁, _, row₁⟩ := hist.row_l hZF ai₀
        obtain ⟨R₂, S₂, V₂, b₂, _, _, _, mi, _, _, _, _, _, _, _, _, hπ₁⟩ := row₁
        obtain ⟨f₀, hf₀⟩ := nice.tree.diagram.map_l hZF hik.1
        have ef₀ := nice.tree.diagram.elementary i k f₀ b₁ X₁ R₂ a X Rx hf₀ hb₁ ha mi.1 mx₀.1
        obtain ⟨q, _, hxq⟩ := ef₀.1.1.2.2 x (hπ₁.1.1.input_mem_of_pairMember hxx)
        obtain ⟨q', _, hqy⟩ := (ultra.elementary_l hZF mx₀.1 mp.1).1.1.2.2 q (ef₀.1.1.output_mem_of_pairMember hxq)
        have eq := (nice.tree.diagram.elementary i m f b₁ X₁ R₂ d P Rp hf hb₁ hd mi.1 mp.1).1.1.1.2 x q' y
          (nice.tree.diagram.comp i k m f₀ j₀ f hf₀ hj₀ hf x q q' hxq hqy) hxy
        obtain ⟨w, hxw, hwy⟩ := (comp.2 x' y').mp hyy
        exact commute q w y y' (hist.squares i k X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α f₀ g₀ ai₀ as hf₀ hg₀ x x' q w hxx hxq hxw)
          (eq ▸ hqy) hwy
  · intro i j k' N₁ B₁ σ₁ u₁ U₁ β₁ X₁ A₁ π₁ z₁ Z₁ α₁ P₁ C₁ τ₁ v₁ V₁ γ₁ p₁ κ₁ ρ₁ F₁ f succ pred' ai ak aj hp pay hf
    rcases (split j).mp (bound aj) with hj' | eq
    · exact hist.steps i j k' N₁ B₁ σ₁ u₁ U₁ β₁ X₁ A₁ π₁ z₁ Z₁ α₁ P₁ C₁ τ₁ v₁ V₁ γ₁ p₁ κ₁ ρ₁ F₁ f succ pred'
        ((old (hist.diagram.order.ordinal.transitive j hj' i succ.predecessor_mem)).mp ai)
        ((old (hist.diagram.order.ordinal.transitive j hj' k' pred'.1)).mp ak) ((old hj').mp aj) hp pay (gold hj' hf)
    · subst j
      have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
      subst i
      have kk : k' = k := by
        have hkw := hω.transitive hZF m hmω k pred.1
        have hkw' := hω.transitive hZF m hmω k' pred'.1
        have forward := ((pred.2 k').mp ((pred'.2 k').mpr (Or.inr (nice.tree.diagram.order.refl k' hkw')))).resolve_left
          (fun eq => ir m (eq ▸ pred'.1))
        have back := ((pred'.2 k).mp ((pred.2 k).mpr (Or.inr (nice.tree.diagram.order.refl k hkw)))).resolve_left
          (fun eq => ir m (eq ▸ pred.1))
        rcases nice.tree.diagram.order.forward k' k forward with eq | lt
        · exact eq
        · exact (nice.tree.diagram.order.forward k k' back).elim Eq.symm
            (fun gt => (ir k ((hω.members_areOrdinals hZF k hkw).transitive k' lt k gt)).elim)
      subst k'
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ((old hm.predecessor_mem).mp ai).unique_l (ZF.modelsKP hZF) hist.function ar
      subst N₁ B₁ σ₁ u₁ U₁ β₁
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ((old pred.1).mp ak).unique_l (ZF.modelsKP hZF) hist.function as
      subst X₁ A₁ π₁ z₁ Z₁ α₁
      obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
      subst P₁ C₁ τ₁ v₁ V₁ γ₁
      have ep := nice.tree.move_function.2 n p₁ p hp he
      subst p₁
      obtain ⟨e₁, e₂, e₃⟩ := pay.unique_l payload
      subst κ₁ ρ₁ F₁
      exact ⟨κ', ρ', F', hκσ, hρσ, hFσ, diagram.map_unique_l hZF hj hf ▸ big, compatible⟩
  · intro i j p' succ hjl hp empty
    rcases (split j).mp hjl with hj' | rfl
    · have hi := hist.diagram.order.ordinal.transitive j hj' i succ.predecessor_mem
      obtain ⟨same, ident⟩ := hist.pads i j p' succ hj' hp empty
      exact ⟨fun r => ((js i r).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hi)).elim), Or.inl⟩).trans
        ((same r).trans ((js j r).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hj')).elim), Or.inl⟩).symm),
        fun f x y hf => ident f x y (gold hj' hf)⟩
    · have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
      subst i
      have eq := nice.tree.move_function.2 n p p' he hp
      obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ payload
      exact (empty u ((pair u).mpr (Or.inl rfl))).elim

end YesMetaZFC.SetTheory.LargeCardinal
