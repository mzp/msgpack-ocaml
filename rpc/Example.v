Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import List String.
Require Import libapplpi.
Require Import Object MultiByte.

Record request : Set := Request {
  request_id : ascii32;
  method : string;
  params : list object
}.

Record response : Set := Response {
  response_id : ascii32;
  error  : object;
  result : object
}.

Record notice : Set := Notice {
  notice_method : string;
  notice_params : list object
}.

Inductive session : Set :=
   Call   (_ : request) (_ : chan response true)
|  Notify (_ : notice).

Inductive either (A B : Set) : Set :=
  Value (_ : A)
| Error (_ : B).

Axiom dispatch : string -> list object -> either object object.


Definition server (ch : chan session true) :=
  ch ??* (fun session =>
    match session with
      | Call req ret =>
        let res :=
          match dispatch (method req) (params req) with
            | Value obj =>
              Response (request_id req) Nil obj
            | Error obj =>
              Response (request_id req) obj Nil
          end in
          OutAtom ret res
      | Notify notify =>
        let _ :=
          dispatch (notice_method notify) (notice_params notify) in
          zeroP
    end
  ).
