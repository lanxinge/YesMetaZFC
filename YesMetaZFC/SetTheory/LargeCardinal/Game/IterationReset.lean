import YesMetaZFC.SetTheory.LargeCardinal.Game.ResetResult
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationStep

/-! # 重置工厂的同一次实际落子与下一有限状态

依次读取恒等延伸、活动复制和回答三段见证。逐层消去存在量词，
保留同一工厂给出的树、末行和实际回答，再调用共同的状态保存定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_reset_native_d.iteration_l
    {ω c₀ X₀ R₀ o C₀ S₀ γ Bγ A x : M.Domain} {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (h : Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A v a)
    (hN : (smdl_structure_l I (R := v 1) h.model.2.1).Models KP)
    (nc : Nonempty {x : (smdl_structure_l I (R := v 1) h.model.2.1).Domain //
      (smdl_structure_l I (R := v 1) h.model.2.1).mem x ⟨v 5,h.request.context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := v 1) h.model.2.1)
      ⟨v 5,h.request.context.member⟩ nc) 46) (eq : ∀ i, (ι.bound i).val.val = a i)
    (reset : Tg_reset_native_d hZF ω c₀ X₀ R₀ (v 7) (v 6) (v 8) (v 9) (v 10) (v 11)
      (v 12) (v 20) (v 22) (v 23) (v 0) (v 1) (v 18) (v 19) (v 24) (v 25) (v 26) (v 15)
      o (v 16) C₀ S₀ γ Bγ (v 2) (v 4) (v 5) (v 3) (v 14) h.model hN h.request.context nc ι)
    (letters : M.mem A Bγ) (hx : M.mem x A) :
    ∃ w b, Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A w b ∧ Tg_iteration_next_d hZF ω c₀ x v w a b := by
  have low : M.PairMember I (v 14) (ι.bound 24).val.val (v 1) :=
    Eq.mpr (congrArg (fun z => M.PairMember I (v 14) z (v 1)) (eq 24)) h.request.below
  exact reset.elim fun θ rest => rest.elim fun T₁ rest => rest.elim fun Q₁ rest => rest.elim fun G₁ rest =>
    rest.elim fun E₁ rest => rest.elim fun j₁ rest => rest.elim fun H₁ rest => rest.elim fun ST₁ rest =>
    rest.elim fun QT₁ rest => rest.elim fun GT₁ rest => rest.elim fun q₁ rest => rest.elim fun _ rest =>
    rest.elim fun mid rest => rest.elim fun first rest => rest.elim fun node₁ rest => rest.elim fun edge₁ rest =>
    rest.elim fun identity rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun history₁ rest =>
    rest.elim fun rows₁ rest => rest.elim fun codes₁ rest => rest.elim fun maps₁ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun ρ rest => rest.elim fun _ rest => rest.elim fun request rest =>
    rest.elim fun _ rest => rest.elim fun length_empty rest => rest.elim fun short_empty rest =>
    rest.elim fun tag_empty rest => rest.elim fun graph_empty rest => rest.elim fun tree_eq rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun L rest =>
    rest.elim fun W rest => rest.elim fun r rest => rest.elim fun _ rest => rest.elim fun code rest =>
    rest.elim fun _ rest => rest.elim fun X rest => rest.elim fun K rest => rest.elim fun R₁ rest =>
    rest.elim fun F rest => rest.elim fun c₁ rest => rest.elim fun d₁ rest => rest.elim fun Y rest =>
    rest.elim fun S rest => rest.elim fun j₀ rest => rest.elim fun κ₁ rest => rest.elim fun U₁ rest =>
    rest.elim fun D₁ rest => rest.elim fun u₁ rest => rest.elim fun _ tail => by
      exact tail.elim fun V rest => rest.elim fun Γ rest => rest.elim fun k rest => rest.elim fun Ls rest =>
        rest.elim fun Js rest => rest.elim fun Os rest => rest.elim fun Zs rest => rest.elim fun Ds rest =>
        rest.elim fun ps rest => rest.elim fun Vs rest => rest.elim fun Ws rest => rest.elim fun qs rest =>
        rest.elim fun d₂ rest => rest.elim fun P rest => rest.elim fun R₂ rest => rest.elim fun j₂ rest =>
        rest.elim fun q₂ rest => rest.elim fun p₂ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
        rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun θ₂ rest => rest.elim fun T₂ rest =>
        rest.elim fun Q₂ rest => rest.elim fun G₂ rest => rest.elim fun E₂ rest => rest.elim fun Λ₂ rest =>
        rest.elim fun H₂ rest => rest.elim fun ST₂ rest => rest.elim fun QT₂ rest => rest.elim fun GT₂ rest =>
        rest.elim fun u₂ rest => rest.elim fun Y₂ rest => rest.elim fun β₂ rest => rest.elim fun B₂ rest =>
        rest.elim fun σ₂ rest => rest.elim fun χ₂ rest => rest.elim fun φ rest => rest.elim fun Uc rest =>
        rest.elim fun Vc rest => rest.elim fun Dc rest => rest.elim fun t rest => rest.elim fun tree₂ rest =>
        rest.elim fun second rest => rest.elim fun critical rest => rest.elim fun qn₂ rest =>
        rest.elim fun edge₂ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun lf₂ rest =>
        rest.elim fun levels₂ rest => rest.elim fun _ rest => rest.elim fun history₂ rest =>
        rest.elim fun rows₂ rest => rest.elim fun codes₂ rest => rest.elim fun maps₂ rest =>
        rest.elim fun last rest => rest.elim fun bound₂ rest => rest.elim fun _ tail => by
          exact tail.elim fun Aₚ rest => rest.elim fun Qₚ rest => rest.elim fun Bₚ rest => rest.elim fun eₚ rest =>
            rest.elim fun Dₚ rest => rest.elim fun Bp rest => rest.elim fun tₚ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun model rest =>
            rest.elim fun w₂ rest => rest.elim fun η₂ rest => rest.elim fun C₂ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun context rest => rest.elim fun nd rest =>
            rest.elim fun ι₂ rest => rest.elim fun ε₂ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun z₂ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun Aq rest =>
            rest.elim fun Uq rest => rest.elim fun Dq rest => rest.elim fun rq rest => rest.elim fun mq rest =>
            rest.elim fun bq rest => rest.elim fun hq rest => rest.elim fun qq rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ ready => by
              have empty_a : a 23 = a 1 :=
                (eq 23).symm.trans ((request 18).symm.trans (tag_empty.trans (eq 1)))
              have below : M.PairMember I (v 14) (ρ.bound 21).val.val (v 1) :=
                Eq.mpr (congrArg (fun z => M.PairMember I (v 14) z (v 1)) (request 14)) low
              have pad := mid.diagram.elementary (v 7) (v 6) j₁ (v 15) (v 0) (v 1)
                (v 15) (v 0) (v 1) edge₁ (first.2.2.1 _ _ h.node) node₁ h.model h.model
              obtain ⟨y,_,point⟩ := pad.1.1.2.2 (ι.bound 7).val.val (ι.bound 7).val.property
              have fixed : M.PairMember I (ι.bound 7).val.val (ι.bound 7).val.val j₁ :=
                (identity _ _ point).symm ▸ point
              have tree_point : M.PairMember I (a 7) (ρ.bound 19).val.val j₁ :=
                Eq.mp (congrArg (fun y => M.PairMember I y (ρ.bound 19).val.val j₁) (eq 7))
                  (Eq.mpr (congrArg (fun y => M.PairMember I (ι.bound 7).val.val y j₁) tree_eq) fixed)
              have parent : Tg_iteration_parent_d hZF v a (v 7) G₁
                  ⟨v 6,v 15,v 0,v 1,v 2,v 4,v 5,L.val,W.val,r,q₁,v 18,v 19⟩ :=
                ⟨j₁,edge₁,Or.inl ⟨empty_a,rfl,(fun i => (ρ.bound i).val.val),code,tree_point,
                  length_empty.trans (request 1).symm,short_empty.trans (request 1).symm,
                  tag_empty.trans (request 1).symm,graph_empty.trans (request 1).symm⟩⟩
              exact h.finish_l hZF mid first tree₂ second lf₂ levels₂ history₂
                (fun z hz => rows₂ z (rows₁ z hz)) (fun z hz => codes₂ z (codes₁ z hz))
                (fun z hz => maps₂ z (maps₁ z hz)) last qn₂ edge₂ bound₂ (critical h.critical) ready.1 (funext eq) parent rfl below letters hx

end YesMetaZFC.SetTheory.LargeCardinal
