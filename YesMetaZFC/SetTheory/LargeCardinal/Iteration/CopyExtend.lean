import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyPadding

/-! # 实际原生复制步装配完整活动历史

新行、工作超幂和交换方块来自同一次复制。历史界由有限端点集构造；
下一支撑在当前原关系中严格高于该界。全部旧行、原树边、共同层及
padding 条件在同一个追加图中同步保持，不把字面高度递增当作原生比较。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 消费现用复制步的实际输出，构造完整的新历史及其最后一行。 -/
theorem Ic_history_d.active_push_l
    {ω c θ T Q G E L n m H S Q' G' k a b d N Rn B σ u U β X Rx A π z Z α
      P Rp C τ v Y γ j j₀ p κ ρ F κ' ρ' F' l₀ A₀ V₀ D₀ t₀ χ : M.Domain}
    (tree : It_tree_d hZF ω c θ T Q G E)
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (pred : It_pred_d T k m)
    (ha : Rd_entry_d k a Q) (hb : Rd_entry_d n b Q) (hd : Rd_entry_d m d Q)
    (hj₀ : It_map_d G k m j₀) (he : Rd_entry_d n p E) (payload : It_payload_d p κ ρ F)
    (hρ : Rd_entry_d n ρ L) (lf : M.IsSetFunction I L)
    (ar : Ic_at_d H n N B σ u U β) (as : Ic_at_d H k X A π z Z α)
    (mx : Smdl_d I a X Rx) (mn : Smdl_d I b N Rn) (mp : Smdl_d I d P Rp)
    (bound : Ic_bound_d I H Q N Rn σ n χ) (above : Rd_entry_d χ ρ Rn)
    (next : Ic_row_d hZF ω d P C τ v Y γ)
    (hκσ : Rd_entry_d κ κ' σ) (hρσ : Rd_entry_d ρ ρ' σ) (hFσ : Rd_entry_d F F' σ)
    (hAC : Rd_entry_d A C j) (big : It_ultra_d I ω κ' ρ' F' z v j)
    (commute : ∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ →
      Rd_entry_d x' y' j → Rd_entry_d y y' τ)
    (compatible : Ea_agree_d ω κ' Z U)
    (quality : Ic_quality_d hZF ω κ' ρ' F' u U)
    (adjacent : Ic_agree_d I N Rn B σ P Rp C τ ρ l₀ ρ' A₀ V₀ D₀ t₀) :
    ∃ l J S' Q'' G'', M.SuccessorOf l m ∧ Ic_history_d hZF ω T Q G E L l J S' Q'' G'' ∧
      M.MemberSubset H J ∧ M.MemberSubset Q' Q'' ∧ M.MemberSubset G' G'' ∧
      Ic_at_d J m P C τ v Y γ ∧ Ic_bound_d I J Q P Rp τ m l₀ := by
  have hω := tree.omega
  have hmθ := (tree.diagram.order.bound k m (tree.diagram.map_bound_l hZF hj₀)).2
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hn
  have eq := hm₀.eq hZF.1 hm
  subst m₀
  obtain ⟨a₀, ha₀, hz, row⟩ := hist.row_l hZF as
  have eq := tree.diagram.model_function.2 k a₀ a ha₀ ha
  subst a₀
  obtain ⟨_, _, Vx, _, _, _, _, _, mz, _, _, _, _, _, _⟩ := row
  have next₀ := next
  obtain ⟨_, Sc, Vy, bc, _, _, _, mc, my, _, _, hC, _, _, hτ⟩ := next₀
  obtain ⟨P₀, Rp₀, _, _, _, mp₀, source, _⟩ := (next.source_l hZF).objects
  obtain ⟨eqP, eqR⟩ := smdl_unique_l I mp₀ mp
  subst P₀ Rp₀
  have past := hist.past_extend_l hZF ar hω hm tree.diagram.model_function hb mn bound mp
    (source.ext.native_l I mp.2.1) hd hρ adjacent above
  have original := tree.diagram.elementary k m j₀ a X Rx d P Rp hj₀ ha hd mx mp
  have supportOrdinal : M.IsOrdinal ρ' := by
    obtain ⟨R,_,trans,model,loc,_,_⟩ := quality
    exact (loc.ordinals_l (ZF.modelsKP hZF) trans ⟨u,model⟩).2
  have strict i X₁ A₁ π₁ z₁ Z₁ α₁ μ φ (ai : Ic_at_d H i X₁ A₁ π₁ z₁ Z₁ α₁)
      (hi : M.mem i n) (hμ : Rd_entry_d i μ L) (image : Rd_entry_d μ φ π₁) : M.mem φ ρ' :=
    hist.support_lt_l hZF hω tree.diagram.model_function lf ar hb mn bound
      hρσ supportOrdinal above ai hi hμ image
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
  have index {i X A π z Z α} (hi : Ic_at_d J i X A π z Z α) : M.mem i l :=
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
          exact ⟨tree.diagram.order.refl m hmθ, hl.predecessor_mem⟩
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
  have result : Ic_history_d hZF ω T Q G E L l J S' Q'' G'' := by
    refine ⟨diagram, order, jf.2.1, jf.2.2, rows, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ai aj hij
      rcases (split j).mp (index aj) with hj | eq
      · exact hist.past i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂
          ((old (hist.diagram.order.ordinal.transitive j hj i hij)).mp ai) ((old hj).mp aj) hij
      · subst j
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
        subst X₂ A₂ π₂ z₂ Z₂ α₂
        exact (past i X₁ A₁ π₁ z₁ Z₁ α₁ ((old hij).mp ai)).1
    · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ai aj hg
      rcases (split j).mp (index aj) with hj' | eq
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
      rcases (split j).mp (index aj) with hj' | eq
      · have hi : M.mem i m := (tree.diagram.order.forward i j (tree.diagram.map_bound_l hZF hf)).elim
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
          exact tree.diagram.identity m f hf x y hxy ▸ diagram.identity m g hg x' y' hyy ▸ hxx
        · have hik := (hist.order i k).mp (hist.diagram.map_bound_l hZF hg₀)
          have ai₀ := (old (hist.diagram.order.bound i k (hist.diagram.map_bound_l hZF hg₀)).1).mp ai
          obtain ⟨b₁, hb₁, _, row₁⟩ := hist.row_l hZF ai₀
          obtain ⟨R₂, S₂, V₂, b₂, _, _, mi, _, _, _, _, _, _, _, hπ₁⟩ := row₁
          obtain ⟨f₀, hf₀⟩ := tree.diagram.map_l hZF hik.1
          have ef₀ := tree.diagram.elementary i k f₀ b₁ X₁ R₂ a X Rx hf₀ hb₁ ha mi mx
          obtain ⟨q, _, hxq⟩ := ef₀.1.1.2.2 x (hπ₁.1.1.input_mem_of_pairMember hxx)
          obtain ⟨q', _, hqy⟩ := original.1.1.2.2 q (ef₀.1.1.output_mem_of_pairMember hxq)
          have eq := (tree.diagram.elementary i m f b₁ X₁ R₂ d P Rp hf hb₁ hd mi mp).1.1.1.2 x q' y
            (tree.diagram.comp i k m f₀ j₀ f hf₀ hj₀ hf x q q' hxq hqy) hxy
          obtain ⟨w, hxw, hwy⟩ := (comp.2 x' y').mp hyy
          exact commute q w y y' (hist.squares i k X₁ A₁ π₁ z₁ Z₁ α₁ X A π z Z α f₀ g₀ ai₀ as hf₀ hg₀ x x' q w hxx hxq hxw)
            (eq ▸ hqy) hwy
    · intro i j k' N₁ B₁ σ₁ u₁ U₁ β₁ X₁ A₁ π₁ z₁ Z₁ α₁ P₁ C₁ τ₁ v₁ V₁ γ₁ p₁ κ₁ ρ₁ F₁ f succ pred' ai ak aj hp pay hf
      rcases (split j).mp (index aj) with hj' | eq
      · exact hist.steps i j k' N₁ B₁ σ₁ u₁ U₁ β₁ X₁ A₁ π₁ z₁ Z₁ α₁ P₁ C₁ τ₁ v₁ V₁ γ₁ p₁ κ₁ ρ₁ F₁ f succ pred'
          ((old (hist.diagram.order.ordinal.transitive j hj' i succ.predecessor_mem)).mp ai)
          ((old (hist.diagram.order.ordinal.transitive j hj' k' pred'.1)).mp ak) ((old hj').mp aj) hp pay (gold hj' hf)
      · subst j
        have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
        subst i
        have kk : k' = k := by
          have hkw := hω.transitive (ZF.modelsKP hZF) m hmω k pred.1
          have forward := ((pred.2 k').mp ((pred'.2 k').mpr (Or.inr (tree.diagram.order.refl k'
            (tree.diagram.order.ordinal.transitive m hmθ k' pred'.1))))).resolve_left
            (fun eq => ir m (eq ▸ pred'.1))
          have back := ((pred'.2 k).mp ((pred.2 k).mpr (Or.inr (tree.diagram.order.refl k
            (tree.diagram.order.ordinal.transitive m hmθ k pred.1))))).resolve_left
            (fun eq => ir m (eq ▸ pred.1))
          rcases tree.diagram.order.forward k' k forward with eq | lt
          · exact eq
          · exact (tree.diagram.order.forward k k' back).elim Eq.symm
              (fun gt => (ir k ((hω.members_areOrdinals (ZF.modelsKP hZF) k hkw).transitive k' lt k gt)).elim)
        subst k'
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ((old hm.predecessor_mem).mp ai).unique_l (ZF.modelsKP hZF) hist.function ar
        subst N₁ B₁ σ₁ u₁ U₁ β₁
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := ((old pred.1).mp ak).unique_l (ZF.modelsKP hZF) hist.function as
        subst X₁ A₁ π₁ z₁ Z₁ α₁
        obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := aj.unique_l (ZF.modelsKP hZF) jf.2.1 top
        subst P₁ C₁ τ₁ v₁ V₁ γ₁
        have ep := tree.move_function.2 n p₁ p hp he
        subst p₁
        obtain ⟨e₁, e₂, e₃⟩ := pay.unique_l payload
        subst κ₁ ρ₁ F₁
        exact ⟨κ', ρ', F', hκσ, hρσ, hFσ, diagram.map_unique_l hZF hj hf ▸ big, compatible, quality⟩
    · intro i j p' succ hjl hp empty
      rcases (split j).mp hjl with hj' | rfl
      · have hi := hist.diagram.order.ordinal.transitive j hj' i succ.predecessor_mem
        obtain ⟨same, ident⟩ := hist.pads i j p' succ hj' hp empty
        exact ⟨fun r => ((js i r).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hi)).elim), Or.inl⟩).trans
          ((same r).trans ((js j r).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hj')).elim), Or.inl⟩).symm),
          fun f x y hf => ident f x y (gold hj' hf)⟩
      · have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
        subst i
        have eq := tree.move_function.2 n p p' he hp
        obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ payload
        exact (empty u ((pair u).mpr (Or.inl rfl))).elim
    · intro i j r X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ μ ψ a₁ b₁ ai aj succ hr hμ hψ ha' hb' hij
      rcases (split r).mp hr with hr | eq
      · have hj := hist.diagram.order.ordinal.transitive r hr j succ.predecessor_mem
        have hi := hist.diagram.order.ordinal.transitive j hj i hij
        exact hist.increasing i j r X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ μ ψ a₁ b₁
          ((old hi).mp ai) ((old hj).mp aj) succ hr hμ hψ ha' hb' hij
      · subst r
        have eq := succ.predecessor_eq hZF.1 (hist.diagram.order.ordinal.mem succ.predecessor_mem) hm
        subst j
        have aj := (old hm.predecessor_mem).mp aj
        obtain ⟨ex, ea, ep, ez, eZ, eα⟩ := aj.unique_l (ZF.modelsKP hZF) hist.function ar
        subst X₂ A₂ π₂ z₂ Z₂ α₂
        have eq := lf.2 n ψ ρ hψ hρ
        subst ψ
        obtain ⟨_, _, _, own⟩ := hist.row_l hZF ar
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, map⟩ := own
        have eq := map.1.1.1.2 ρ b₁ ρ' hb' hρσ
        subst b₁
        exact strict i X₁ A₁ π₁ z₁ Z₁ α₁ μ a₁ ((old ((hm i).mpr (Or.inl hij))).mp ai) hij hμ ha'
  -- 新相邻端点自身出现于端点集，所有旧端点由复合落在它以下。
  have ord := adjacent.right_ord_l hZF hω mp mc hτ
  have height : Ic_height_d I J Q P Rp τ m n l₀ :=
    ⟨ord, N, B, σ, u, U, β, C, v, Y, γ, b, d, Rn, ρ, ρ', A₀, V₀, D₀, t₀,
      (old hm.predecessor_mem).mpr ar, top, hb, hd, mn, mp, adjacent⟩
  have bnd : Ic_bound_d I J Q P Rp τ m l₀ := by
    refine ⟨ord, Or.inr ⟨n, hm.predecessor_mem, height⟩, ?_⟩
    intro i a hi ha
    obtain ⟨_, X₁, A₁, π₁, z₁, Z₁, α₁, ai, _, _, _⟩ := hist.at_l hZF hi
    obtain ⟨ρ₁, l₁, φ₁, V₁, V₂, D₁, t₁, c₁, R₁, qi, mi, same, le⟩ :=
      (past i X₁ A₁ π₁ z₁ Z₁ α₁ ai).2
    have end₁ : Ic_height_d I J Q P Rp τ m i l₁ :=
      ⟨same.right_ord_l hZF hω mp mc hτ,
        X₁, A₁, π₁, z₁, Z₁, α₁, C, v, Y, γ, c₁, d, R₁, ρ₁, φ₁, V₁, V₂, D₁, t₁,
        (old hi).mpr ai, top, qi, hd, mi, mp, same⟩
    exact (result.height_unique_l hZF hω tree.diagram.model_function ha end₁).symm ▸ le
  exact ⟨l, J, S', Q'', G'', hl, result, sub hist.function.1 jm,
    sub hist.diagram.model_function.1 (fun i a ha => (qs i a).mpr (Or.inl ha)),
    sub hist.diagram.map_function.1 gm, top, bnd⟩

section
variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 同一原后继、完整池和共同层先产生实际复制行，随后直接装配整份历史。 -/
theorem Ic_history_d.copy_step_l
    {c₀ θ T Q G E Λ n m JH ST QT GT k p χ : M.Domain}
    {ω c X A π z Z α b Ns B σ u U β Rₕ Rₓ κ L F o P Rₚ j₀ zs Γ ks
      Vₚ Ls Js Os Zs Ds ps Vs Ws qs D₀ η Dp Bp t₀ l U₁ V₂ Γ₁ k₁ : M.Domain}
    (mx : Smdl_d J c X Rₓ) (mh : Smdl_d J b Ns Rₕ)
    (hN : (smdl_structure_l J (R := Rₕ) mh.2.1).Models KP)
    (w ξ ℓ e X₀ δ K₀ R₀ U₀ β₀ A₀ Q₀ B₀ e₀ : (smdl_structure_l J (R := Rₕ) mh.2.1).Domain)
    (numbers : Rr_layer_d J ω Ns Rₕ w.val zs) (source : Ep_source_d (kp_pair_l hN) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hN) δ X₀) (height : (smdl_structure_l J (R := Rₕ) mh.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w X₀ R₀ ξ ℓ e)
    (quality : It_owner_d J ω b ξ.val ℓ.val e.val)
    (hξ : Rd_entry_d ξ.val κ σ) (hℓ : Rd_entry_d ℓ.val L σ) (he : Rd_entry_d e.val F σ)
    (finite : Fs_read_d w U₀) (owner_closed : Rr_closed_d J Ns Rₕ U₀.val)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x Ns ∧ Rd_entry_d x U₀.val Rₕ)
    (hU : Rd_entry_d U₀.val D₀ σ) (hD : M.mem D₀ A)
    (rA : Vr_d A η D₀) (rB : Vr_d B η D₀) (hη : M.IsLimitOrdinal η)
    (agreement : Er_agree_d J ω Ns Rₕ ξ.val zs Γ X Rₓ ks)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y ks → Rd_entry_d y x' π)
    (parent_image : ∀ y, Rd_entry_d y Vₚ Rₓ ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks)
    (parent_small : Rr_small_d J X Rₓ Vₚ)
    (hβU : (smdl_structure_l J (R := Rₕ) mh.2.1).mem β₀ U₀)
    (hβX : (smdl_structure_l J (R := Rₕ) mh.2.1).mem β₀ X₀)
    (transβ : (smdl_structure_l J (R := Rₕ) mh.2.1).TransitiveSet β₀)
    (products : ∀ m D : (smdl_structure_l J (R := Rₕ) mh.2.1).Domain,
      (smdl_structure_l J (R := Rₕ) mh.2.1).mem m w → Ep_space_d ξ m D →
        ∃ P, (smdl_structure_l J (R := Rₕ) mh.2.1).mem P U₀ ∧
          (smdl_structure_l J (R := Rₕ) mh.2.1).IsCartesianProduct (kp_pair_l hN) P D β₀)
    (pool : Eb_collapse_d w ξ ℓ K₀ X₀ β₀ e A₀ Q₀ B₀ e₀)
    (dc : ∀ x, M.mem x Dp ↔ M.mem x Ns ∧ Rd_entry_d x A₀.val Rₕ)
    (bc : ∀ x, M.mem x Bp ↔ M.mem x Ns ∧ Rd_entry_d x B₀.val Rₕ)
    (ft : Fn0_d Bp P t₀) (present : Er_present_d J ω Ls Ns Rₕ zs Γ X ks qs e₀.val Dp t₀)
    (prepare : ∀ v : (smdl_structure_l J (R := Rₕ) mh.2.1).Domain,
      (smdl_structure_l J (R := Rₕ) mh.2.1).mem v A₀ →
      ∃ α, ∃ m a D f : (smdl_structure_l J (R := Rₕ) mh.2.1).Domain,
        Ei_d ω Ls α ∧ Rr_finite_d J ω Ls Ns Rₕ zs α a.val ∧
        (smdl_structure_l J (R := Rₕ) mh.2.1).mem m w ∧ Fn0_d m ℓ a ∧ Ep_space_d ξ m D ∧
        (smdl_structure_l J (R := Rₕ) mh.2.1).mem f U₀ ∧ Fn0_d D β₀ f ∧
        KPair_d (smdl_structure_l J (R := Rₕ) mh.2.1) v a f)
    (length : ∀ x, M.mem x Ls ↔ M.mem x Ns ∧ Rd_entry_d x ℓ.val Rₕ)
    (raw : Er_graph_d J ω Ls Ns Rₕ ξ.val ℓ.val e.val zs X Rₓ ks Js Os Zs Ds ps Vs Ws)
    (diagram : Di_system_d Js Os Ds ps Vs Ws) (limit : Di_limit_d Ds ps Vs Ws qs P Rₚ)
    (original : Smdl_d J o P Rₚ) (fj : Fn0_d X P j₀) (cj : Er_constants_d X qs j₀)
    (new_common : Ic_common_d J Ns Rₕ P Rₚ ℓ.val l U₁ V₂ Γ₁ k₁)
    (restrict : M.IsRestrictionOf J k₁ t₀ Γ₁)
    (endpoint : Rd_entry_d ℓ.val l t₀) (layer : Rd_entry_d U₁ V₂ t₀)
    (tree : It_tree_d hZ ω c₀ θ T Q G E)
    (hist : Ic_history_d hZ ω T Q G E Λ m JH ST QT GT)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (pred : It_pred_d T k m)
    (hc : Rd_entry_d k c Q) (hb : Rd_entry_d n b Q) (ho : Rd_entry_d m o Q)
    (edge : It_map_d G k m j₀) (move : Rd_entry_d n p E)
    (payload : It_payload_d p ξ.val ℓ.val e.val) (active : Rd_entry_d n ℓ.val Λ) (lf : M.IsSetFunction J Λ)
    (ai : Ic_at_d JH k X A π z Z α) (an : Ic_at_d JH n Ns B σ u U β)
    (bound : Ic_bound_d J JH Q Ns Rₕ σ n χ) (above : Rd_entry_d χ ℓ.val Rₕ) :
    ∃ Y v C γ τ r JH' ST' QT' GT', M.SuccessorOf r m ∧
      Ic_history_d hZ ω T Q G E Λ r JH' ST' QT' GT' ∧
      M.MemberSubset JH JH' ∧ M.MemberSubset QT QT' ∧ M.MemberSubset GT GT' ∧
      Ic_at_d JH' m P C τ v Y γ ∧ Ic_bound_d J JH' Q P Rₚ τ m l ∧
      Ic_agree_d J Ns Rₕ B σ P Rₚ C τ ℓ.val l L U₁ V₂ Γ₁ k₁ := by
  obtain ⟨c', hc', _, row⟩ := hist.row_l hZ ai
  have eq := tree.diagram.model_function.2 k c' c hc' hc
  subst c'
  obtain ⟨b', hb', _, own⟩ := hist.row_l hZ an
  have eq := tree.diagram.model_function.2 n b' b hb' hb
  subst b'
  obtain ⟨Y, v, C, γ, j, τ, next, _, hAC, big, commute, _, _, compatible, _, adjacent, quality⟩ :=
    row.step_l hZFC own mx mh hN w ξ ℓ e X₀ δ K₀ R₀ U₀ β₀ A₀ Q₀ B₀ e₀
      numbers source rank height loc quality hξ hℓ he finite owner_closed carrier hU hD rA rB hη
      agreement square parent_image parent_small hβU hβX transβ products pool dc bc ft present prepare
      length raw diagram limit original fj cj new_common restrict endpoint layer
  obtain ⟨Rᵤ, mu, up, strong, card, _⟩ := quality
  obtain ⟨_, _, _, _, _, _, _, _, _, _, full, _, _, _, _⟩ := own
  have quality : Ic_quality_d hZ ω κ L F u U :=
    ⟨Rᵤ, full.source.omega, full.source.transitive, mu, up, strong, card⟩
  obtain ⟨r, JH', ST', QT', GT', succ, updated, rows, codes, maps, last, bnd⟩ :=
    hist.active_push_l hZ tree hn hm pred hc hb ho edge move payload active lf an ai mx mh original
      bound above next hξ hℓ he hAC big commute compatible quality adjacent
  exact ⟨Y, v, C, γ, τ, r, JH', ST', QT', GT', succ, updated, rows, codes, maps, last, bnd, adjacent⟩

end

end YesMetaZFC.SetTheory.LargeCardinal
