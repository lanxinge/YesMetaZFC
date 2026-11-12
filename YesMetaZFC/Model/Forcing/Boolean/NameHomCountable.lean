import YesMetaZFC.Model.Forcing.Boolean.NameHomData

/-! # 可数反射模型中的命中图完全性

可数性只用于在反例条件下构造泛型；主定理随后用原公式反射消去它。
任意内部上确界的保持直接消费小泛型对原模型稠密集的命中性质。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {B R z b p Q T w 𝒟 τ K S e C L V d F : M.Domain}

theorem Nh_d.read_l (h : Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hp : G p) :
    ∃ H : M.Domain → Prop, Generic_d M Q T w H ∧
      (∀ q, H q ↔ ∃ a, Check_d M b q a ∧ ∃ r, G r ∧ Mem_force_d M B R z r a τ) ∧
      ∀ U X, Entry_d M U X F → ((∃ q, G q ∧ M.mem q X) ↔ ∃ q, H q ∧ M.mem q U) := by
  have hb := generic.upward p b hp h.base h.below
  obtain ⟨Y,value⟩ := name_value_l (R := R) (z := z) (U := G) h.name.1
  obtain ⟨j,checks,full,inj⟩ := check_map_l h.big hZF generic hb
  have small := h.name.value_l hZF h.big h.power generic hp value j inj full checks
  refine ⟨_,small,?_,fun U X ux => ?_⟩
  · intro q
    constructor
    · intro hq
      obtain ⟨a,check,_,_⟩ := zf_check_l M hZF h.base q
      exact ⟨a,check,(qval_mem_forcing_l h.big hZF generic (checks q a check) value).mpr hq⟩
    · rintro ⟨a,check,hit⟩
      exact (qval_mem_forcing_l h.big hZF generic (checks q a check) value).mp hit
  · obtain ⟨W,truth,inter⟩ := h.graph U X ux
    have hits := ropen_hit_inter_l (truth.regular_l hZF h.big h.base h.name.1) h.cone inter generic
    apply hits.trans ((and_iff_left ⟨p,hp,h.point⟩).trans ?_)
    exact (truth.value_l hZF h.big generic hb value j full checks).trans
      (exists_congr fun q => and_comm)

theorem Nh_d.meet_values_l (h : Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F)
    {X Y Z : M.Domain} (hx : M.mem X L) (hy : M.mem Y L) (meet : BooleanZF.Meet_d I L V X Y Z) :
    ∀ q, M.mem q Z ↔ M.mem q X ∧ M.mem q Y := by
  obtain ⟨W,regular,values⟩ := ropen_inter_l hZF ((h.localFamily X).mp hx).1 ((h.localFamily Y).mp hy).1
  have hw := (h.localFamily W).mpr ⟨regular,fun q hq => ((h.localFamily X).mp hx).2 q ((values q).mp hq).1⟩
  have wz := (meet.2 W hw).mpr ⟨(h.localOrder W X hw hx).mpr (fun q hq => ((values q).mp hq).1),
    (h.localOrder W Y hw hy).mpr (fun q hq => ((values q).mp hq).2)⟩
  have bounds := BooleanZF.meet_bounds_d I h.target.order meet
  exact fun q => ⟨fun hq => ⟨(h.localOrder Z X meet.1 hx).mp bounds.1 q hq,
    (h.localOrder Z Y meet.1 hy).mp bounds.2 q hq⟩,
    fun hq => (h.localOrder W Z hw meet.1).mp wz q ((values q).mpr hq)⟩

theorem Nh_d.test_l (h : Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F)
    (f : Nat → M.Domain) (onto : Function.Surjective f) {X Y : M.Domain} (hx : M.mem X L) (hy : M.mem Y L) :
    Entry_d M X Y V ↔ ∀ G, Generic_d M B R z G → G p →
      (∃ q, G q ∧ M.mem q X) → ∃ q, G q ∧ M.mem q Y := by
  apply (h.localOrder X Y hx hy).trans
  refine ⟨fun sub G _ _ ⟨q,hq,qx⟩ => ⟨q,hq,sub q qx⟩,fun test => ?_⟩
  exact ropen_countable_le_l hZF h.big f onto h.positive.1 h.positive.2 h.point h.minimal
    ((h.localFamily X).mp hx).1 ((h.localFamily Y).mp hy).1 ((h.localFamily X).mp hx).2 test

theorem Nh_d.countable_complete_l (h : Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F)
    (f : Nat → M.Domain) (onto : Function.Surjective f) : BooleanZF.Cbh_d I K S e L V d F := by
  have out {U X} (ux : Entry_d M U X F) := h.function.output_mem_of_pairMember ux
  have inp {U X} (ux : Entry_d M U X F) := h.function.input_mem_of_pairMember ux
  have test {X Y} (hx : M.mem X L) (hy : M.mem Y L) := h.test_l hZF f onto hx hy
  have hitMeet {X Y Z} (hx : M.mem X L) (hy : M.mem Y L) (meet : BooleanZF.Meet_d I L V X Y Z)
      {G : M.Domain → Prop} (generic : Generic_d M B R z G) :=
    ropen_hit_inter_l ((h.localFamily X).mp hx).1 ((h.localFamily Y).mp hy).1
      (h.meet_values_l hZF hx hy meet) generic
  refine ⟨⟨h.function,?_,?_,?_⟩,?_⟩
  · obtain ⟨X,hx,ex⟩ := h.function.2.2 e h.source.bot_mem
    have xd := (test hx h.target.bot_mem).mpr (by
      intro G generic hp hit
      obtain ⟨H,_,_,read⟩ := h.read_l hZF generic hp
      obtain ⟨q,_,qe⟩ := (read e X ex).mp hit
      exact (h.empty q qe).elim)
    have eq := h.target.order.antisymm X d hx h.target.bot_mem xd (h.target.bot_le X hx)
    exact eq ▸ ex
  · intro A A₂ D X Y Z ax ay dz meet
    have semantic G (generic : Generic_d M B R z G) (hp : G p) :
        (∃ q, G q ∧ M.mem q Z) ↔ (∃ q, G q ∧ M.mem q X) ∧ ∃ q, G q ∧ M.mem q Y := by
      obtain ⟨H,small,_,read⟩ := h.read_l hZF generic hp
      have inter := ropen_meet_values_l hZF h.family h.order h.source.toBoolean_d (inp ax) (inp ay) meet
      exact (read D Z dz).trans ((ropen_hit_inter_l ((h.family A).mp (inp ax))
        ((h.family A₂).mp (inp ay)) inter small).trans (and_congr (read A X ax).symm (read A₂ Y ay).symm))
    refine ⟨out dz,fun W hw => ⟨fun wz => ⟨?_,?_⟩,?_⟩⟩
    · exact (test hw (out ax)).mpr (fun G generic hp hit =>
        ((semantic G generic hp).mp ((test hw (out dz)).mp wz G generic hp hit)).1)
    · exact (test hw (out ay)).mpr (fun G generic hp hit =>
        ((semantic G generic hp).mp ((test hw (out dz)).mp wz G generic hp hit)).2)
    · rintro ⟨wx,wy⟩
      exact (test hw (out dz)).mpr (fun G generic hp hit => (semantic G generic hp).mpr
        ⟨(test hw (out ax)).mp wx G generic hp hit,(test hw (out ay)).mp wy G generic hp hit⟩)
  · intro A N X Y ax ny neg
    have semantic G (generic : Generic_d M B R z G) (hp : G p) :
        (∃ q, G q ∧ M.mem q Y) ↔ ¬ ∃ q, G q ∧ M.mem q X := by
      obtain ⟨H,small,_,read⟩ := h.read_l hZF generic hp
      exact (read N Y ny).trans ((ropen_hit_neg_l hZF h.small h.family h.order small h.source.toBoolean_d h.empty (inp ax) neg).trans
        (not_congr (read A X ax).symm))
    refine ⟨out ny,fun W hw => ⟨?_,?_⟩⟩
    · intro wy Z meet
      apply (test meet.1 h.target.bot_mem).mpr
      intro G generic hp hit
      obtain ⟨hitW,hitX⟩ := (hitMeet hw (out ax) meet generic).mp hit
      exact ((semantic G generic hp).mp ((test hw (out ny)).mp wy G generic hp hitW) hitX).elim
    · intro all
      obtain ⟨Z,meet⟩ := h.target.meet W X hw (out ax)
      apply (test hw (out ny)).mpr
      intro G generic hp hitW
      apply (semantic G generic hp).mpr
      intro hitX
      obtain ⟨q,_,qd⟩ := (test meet.1 h.target.bot_mem).mp (all Z meet) G generic hp
        ((hitMeet hw (out ax) meet generic).mpr ⟨hitW,hitX⟩)
      exact h.localEmpty q qd
  · intro D A X sub sup ax
    constructor
    · intro U Y hu uy
      apply (test (out uy) (out ax)).mpr
      intro G generic hp hitY
      obtain ⟨H,_,_,read⟩ := h.read_l hZF generic hp
      obtain ⟨q,hq,qu⟩ := (read U Y uy).mp hitY
      exact (read A X ax).mpr ⟨q,hq,((h.order U A).mp (sup.2.1 U hu)).2.2 q qu⟩
    · intro Z hz upper
      apply (test (out ax) hz).mpr
      intro G generic hp hitX
      obtain ⟨H,small,_,read⟩ := h.read_l hZF generic hp
      obtain ⟨U,hu,hitU⟩ := (ropen_hit_sup_l hZF h.small h.family h.order small h.source.order sub sup).mp ((read A X ax).mp hitX)
      obtain ⟨Y,hy,uy⟩ := h.function.2.2 U (sub U hu)
      exact (test hy hz).mp (upper U Y hu uy) G generic hp ((read U Y uy).mpr hitU)

end YesMetaZFC.Model.Forcing.Internal
