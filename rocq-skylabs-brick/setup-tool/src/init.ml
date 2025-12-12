open Panic

let command : Project.br_project -> unit = fun config ->
  begin
    match Project.locate_root () with None -> () | Some(root,_) ->
    panic "Error: you are running the command from within a project.\n\
      The project root is [%s]." root
  end;
  Project.write_br_project Project.project_file_name config
