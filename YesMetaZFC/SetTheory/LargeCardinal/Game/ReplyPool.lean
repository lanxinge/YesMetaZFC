import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyReflect
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence

/-! # 同一有界池中的完整规则 (7)

原极限切片的相对秩历史沿本次超幂搬运，给出所选池自身的分离和配对闭包。
完整回答的投影与子类型见证由这些实际闭包回收，不能另取一个回答超幂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 规则 (7) 的统一参数顺序；七个程序槽位仍是所属模型中的实际对象。 -/
def tg_reply_values_d {α : Type u} (ω l n κ τ U D Q u w b z r q h : α) (σ : Fin 7 → α) : Fin 22 → α :=
  fun i => [ω,l,n,κ,τ,U,D,Q,u,w,b,z,r,q,h,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i

/-- 完整轮记录中的回答坐标；临界点与三份超幂像由该轮的固定证书指定。 -/
def tg_round_reply_values_d {α : Type u} (v : Fin 54 → α) (ω κ U D u : α) : Fin 22 → α :=
  tg_reply_values_d ω (v 23) (v 24) κ (v 15) U D (v 12) u (v 11) (v 36) (v 38)
    (v 2) (v 1) (v 0) (fun i => v ([47,48,49,50,51,52,53].get i))

theorem Tg_image_at_d.reply_pool_l
    {ω κ δ l n U D u τ Q w b z L W X K R F c d Y S j κ' U' D' u' α β A T B e : M.Domain}
    {σ : Fin 7 → M.Domain} {p : Tg_reply_queries_d M}
    (image : Tg_image_at_d (ZF.modelsKP hZF) ω κ δ l n U D u τ Q w b σ z p
      L W X K R F c d Y S j κ' U' D' u')
    (height : M.IsLimitOrdinal δ) (rank : V_d I α β) (limit : M.IsLimitOrdinal α)
    (below : M.mem α δ) (hU : M.mem U β) (hD : M.mem D β) (hu : M.mem u β)
    (owned : Eb_collapse_d ω κ L K X β F A T B e) (hWB : M.mem W B)
    (hb : M.mem b ω) (hz : M.mem z ω) (hσ : ∀ i, M.mem (σ i) ω) :
    M.TransitiveSet B ∧ (∀ a b, M.mem a B → M.mem b B → ∃ p, M.mem p B ∧ Pair_d M p a b) ∧
    ∃ nb : Nonempty {x // M.mem x B}, ∃ ρ : Env (rt_model_l B nb) 22,
      (∀ i, (ρ.bound i).val = tg_reply_values_d ω l n κ' τ U' D' Q u' w b z p.root p.bound p.height σ i) ∧
      Formula.satisfies ρ tg_reply0_m := by
  obtain ⟨rankX, source, _, _, _, _, hQW, loc, _, _, mx, my, ultra, critical, _, hκ',
    iU, iD, iu, _, reply⟩ := image
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (fun _ D _ hD _ => sc_v_power_l (ZF.modelsKP hZF) height rankX D hD)
  have hj := ultra.elementary_l hZF mx.1 my.1
  have yt := ultra.transitive_l hZF my.1
  have hβX := ZF.v_mem_l I hZF rank rankX below
  have iβ := (owned.image_l hZF source family mx my ultra hβX (v_transitive_l I rank)).1
  have hBY := hj.1.1.output_mem_of_pairMember iβ
  obtain ⟨a, _, ia⟩ := hj.1.1.2.2 α (KP.v_ordinal_subset_l (ZF.modelsKP hZF) rankX α below)
  obtain ⟨Z, f, hZ, hf, history, _⟩ := vr_source_l hZF rankX height below rank
  have relative : Vr_d X α β := ⟨Z, f, hZ, hf, fun x _ => history x⟩
  have rankB := (hj.hierarchy_l hZF source.omega source.transitive yt mx my ia iβ).mp relative
  have limitB := (hj.limit_l hZF source.omega source.transitive yt mx my ia).mp limit
  have bt := rankB.transitive_l yt hBY
  have theory := source.theory.map_l I hZF source.omega mx.1 my.1 hj
  obtain ⟨K', target⟩ := source.successor_l hZF mx my yt hj
    (hj.1.1.output_mem_of_pairMember critical.image)
    (source.omega.subset_limitOrdinal (ZF.modelsKP hZF) hκ')
    (sc_ordinal_small_l hZF source.omega yt my theory
      (hj.1.1.output_mem_of_pairMember critical.image) hκ'.1)
  have hU' := (hj.member_l I hZF source.omega mx my iU iβ).mp hU
  have hD' := (hj.member_l I hZF source.omega mx my iD iβ).mp hD
  have hu' := (hj.member_l I hZF source.omega mx my iu iβ).mp hu
  have data := reply
  obtain ⟨_, v, _, ⟨_, _, q, query, _⟩, hr, hq, hh⟩ := data
  obtain ⟨hw, hn, hl, hτ, hk, hω⟩ := query.constants
  have low x (hx : M.mem x U') := bt U' hU' x hx
  have small x (hx : M.mem x ω) := bt ω (low ω hω) x hx
  let values : Fin 22 → M.Domain := fun i =>
    [ω,l,n,κ',τ,U',D',Q,u',w,b,z,p.root,p.bound,p.height,
      σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i
  have members : ∀ i, M.mem (values i) B := by
    simp only [Fin.forall_fin_succ]
    exact ⟨low ω hω, low l hl, low n hn, low κ' hk, low τ hτ, hU', hD', bt W hWB Q hQW,
      hu', low w hw, small b hb, small z hz, bt w (low w hw) _ hr,
      bt w (low w hw) _ hq, bt w (low w hw) _ hh,
      small _ (hσ 0), small _ (hσ 1), small _ (hσ 2), small _ (hσ 3),
      small _ (hσ 4), small _ (hσ 5), small _ (hσ 6), fun i => Fin.elim0 i⟩
  obtain ⟨cB, RB, modelB⟩ := smdl_membership_l I hZF ⟨ω, members 0⟩
  have theoryB := target.rank_theory_l hZF hBY rankB limitB modelB
  let nb : Nonempty {x // M.mem x B} := ⟨⟨ω, members 0⟩⟩
  let ρ : Env (rt_model_l B nb) 22 := ⟨fun i => ⟨values i, members i⟩, fun _ => ⟨ω, members 0⟩⟩
  let slots : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have eq : (fun i => ((slots i).eval ρ).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))) i
  refine ⟨bt, (theoryB.algebra_l _ (ZF.modelsKP hZF) bt modelB).pair, nb, ρ, fun _ => rfl, ?_⟩
  apply tg_reply_reflect_l hZF source.omega bt modelB theoryB nb ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
    (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) slots
  exact eq.symm ▸ reply

end YesMetaZFC.SetTheory.LargeCardinal
