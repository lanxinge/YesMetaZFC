import YesMetaZFC.SetTheory.LargeCardinal.Demand.SeparatedGame
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ReadyStep
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift

/-! # 原 I 胜策自动给出一个实际实数字母

II 的真实合法重置后，I 必须依次合法回答并落下首个实数字母。
因此泛型策略构造不必另加 A 非空；空 A 时原 I 胜策前提自行矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_game_d.first_letter_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hd : Woodin_d I p.δ)
    (root : M.mem p.e p.S) (win : Cg_win_d I true p.ω X F J B W σ) : ∃ a, M.mem a p.A := by
  obtain ⟨R,control⟩ := game.control_l hZFC win
  have emptyFn : Fn0_d p.e X p.e := ⟨fun x hx => (game.setup.empty x hx).elim,
    fun x hx => (game.setup.empty x hx).elim,fun x hx => (game.setup.empty x hx).elim⟩
  have ready := game.setup.ready_empty_l hZFC
  have initial := ready
  obtain ⟨heω,i,z,hiω,fh,div,_,_⟩ := initial
  have ei := fh.domain_eq_l hZF.1 emptyFn
  subst i
  obtain ⟨v,hv,aux⟩ := game.setup.ready_move_l hZFC hd root ready
  have push {i j h x : M.Domain} (hi : M.mem i p.ω) (succ : M.SuccessorOf j i)
      (fh : Fn0_d i X h) (hx : M.mem x X) :
      ∃ t, Fn0_d j X t ∧ M.mem t F ∧ Fseq_end_d I p.ω t h x := by
    obtain ⟨j',t,hj,ft,et⟩ := ZF.fseq_end_exists_l I hZF game.setup.omega hi
      (fn0_function_l (ZF.modelsKP hZF) fh) hx
    obtain ⟨m,n,d⟩ := et
    have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
    have ej := d.source.2.2.2.eq hZF.1 ft.2.1
    have sj : M.SuccessorOf j' i := ej ▸ ei ▸ d.length_successor
    have eq := sj.eq hZF.1 succ
    exact ⟨t,fn0_of_function_l (ZF.modelsKP hZF) (eq ▸ ft),
      (game.histories.1 t).mpr ⟨j,eq ▸ hj,eq ▸ ft⟩,m,n,d⟩
  obtain ⟨h₁,fh₁,h₁F,end₁⟩ := push heω game.setup.one emptyFn hv
  have fs := fn0_function_l (ZF.modelsKP hZF) control.strategy
  obtain ⟨b,hb,value₁⟩ := fs.2.2 h₁ h₁F
  obtain ⟨one,sone,hone⟩ := game.setup.omega.1.2 p.e heω
  have eo := sone.eq hZF.1 game.setup.one
  subst one
  obtain ⟨h₂,fh₂,h₂F,end₂⟩ := push hone game.setup.two fh₁ hb
  obtain ⟨y,hy,value₂⟩ := fs.2.2 h₂ h₂F
  obtain ⟨two,stwo,htwo⟩ := game.setup.omega.1.2 p.a hone
  have et := stwo.eq hZF.1 game.setup.two
  subst two
  obtain ⟨t,_,tF,end₃⟩ := push htwo game.setup.three fh₂ hy
  obtain ⟨hc,_⟩ := tg_clock_l hZF game.setup.omega game.setup.empty game.setup.one game.setup.two game.setup.three heω
  have oc := game.setup.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ab := oc.transitive p.b game.setup.three.predecessor_mem p.a game.setup.two.predecessor_mem
  have div₁ := tg_division_next_l hZF oc div game.setup.one game.setup.one ab
  have div₂ := tg_division_next_l hZF oc div₁ game.setup.two game.setup.two game.setup.three.predecessor_mem
  have turn := (game.owner.read_l hZF (game.setup.omega.isOrdinal (ZF.modelsKP hZF)) oc
    ⟨p.b,game.setup.three.predecessor_mem⟩ htwo heω div₂).mpr
    (Or.inr ⟨rfl,gm_even_zero_l I hZF game.setup.omega game.setup.empty⟩)
  have legal := game.histories.admit_l hZF game.setup.omega heω heω emptyFn div hv aux
  obtain ⟨_,_,_,_,hyA,_⟩ := ready.advance_l hZFC game.setup game.histories game.owner control
    control.root game.setup.one h₁F h₂F tF end₁ end₂ end₃ legal value₁ ⟨p.b,fh₂,Or.inl ⟨turn,value₂⟩⟩
  exact ⟨y,hyA⟩

end YesMetaZFC.SetTheory.LargeCardinal
